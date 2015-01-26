# Copyright (C) 2005 Christian Limpach <Christian.Limpach@cl.cam.ac.uk>
# Copyright (C) 2005 XenSource Ltd

# This file is subject to the terms and conditions of the GNU General
# Public License.  See the file "COPYING" in the main directory of
# this archive for more details.

import os
import os.path
import re
import string
import threading
import time
import fcntl
from struct import pack, unpack, calcsize

from xen.util.xpopen import xPopen3
import xen.util.auxbin
import xen.lowlevel.xc

from xen.xend import balloon, sxp, image
from xen.xend.XendError import XendError, VmError
from xen.xend.XendLogging import log
from xen.xend.XendConfig import XendConfig
from xen.xend.XendConstants import *

SIGNATURE = "LinuxGuestRecord"
QEMU_SIGNATURE = "QemuDeviceModelRecord"
dm_batch = 512
XC_SAVE = "xc_save"
XC_RESTORE = "xc_restore"


sizeof_int = calcsize("i")
sizeof_unsigned_int = calcsize("I")
sizeof_unsigned_long = calcsize("L")


xc = xen.lowlevel.xc.xc()


def write_exact(fd, buf, errmsg):
    if os.write(fd, buf) != len(buf):
        raise XendError(errmsg)


def read_exact(fd, size, errmsg):
    buf  = '' 
    while size != 0: 
        readstr = os.read(fd, size)
        if not len(readstr):
            log.error("read_exact: EOF trying to read %d (buf='%s')" % \
                      (size, buf))
            raise XendError(errmsg)
        size = size - len(readstr)
        buf  = buf + readstr
    return buf


def save(fd, dominfo, network, live, dst, checkpoint=False):
    write_exact(fd, SIGNATURE, "could not write guest state file: signature")
    
    # CoW timing
    checkpointtime = []
    downtime = []

    buf_list = []

    # Cow timing
    checkpointtime.append(time.time())

    config = sxp.to_string(dominfo.sxpr())

    domain_name = dominfo.getName()
    # Rename the domain temporarily, so that we don't get a name clash if this
    # domain is migrating (live or non-live) to the local host.  Doing such a
    # thing is useful for debugging.
    dominfo.setName('migrating-' + domain_name)

    try:
        dominfo.migrateDevices(network, dst, DEV_MIGRATE_STEP1, domain_name)

        write_exact(fd, pack("!i", len(config)),
                    "could not write guest state file: config len")
        write_exact(fd, config, "could not write guest state file: config")

        image_cfg = dominfo.info.get('image', {})
        hvm = dominfo.info.is_hvm()

        # xc_save takes three customization parameters: maxit, max_f, and
        # flags the last controls whether or not save is 'live', while the
        # first two further customize behaviour when 'live' save is
        # enabled. Passing "0" simply uses the defaults compiled into
        # libxenguest; see the comments and/or code in xc_linux_save() for
        # more information.
        cmd = [xen.util.auxbin.pathTo(XC_SAVE), str(fd),
               str(dominfo.getDomid()), "0", "0", 
               str(int(live) | (int(hvm) << 2)) ]

        def saveInputHandler(line, tochild):
            if line == "suspend":
                dominfo.shutdown('suspend')

                # CoW timing
                downtime.append(time.time())
    
                dominfo.waitForShutdown()
                dominfo.migrateDevices(network, dst, DEV_MIGRATE_STEP2,
                                       domain_name)
                dominfo.migrateDevices(network, dst, DEV_MIGRATE_STEP3,
                                       domain_name)
                if hvm:
                    dominfo.image.saveDeviceModel()

                    # for CoW purposes, get qemu-dm state
	            qemu_fd = os.open("/var/lib/xen/qemu-save.%d" % dominfo.getDomid(), os.O_RDONLY)
	            while True:
	                buf = os.read(qemu_fd, dm_batch)
	                if len(buf):
	                    buf_list.append(buf)
	                else:
	                    break
	            os.close(qemu_fd)

                # Cow: snapshot VBD
                os.system("/etc/xen/scripts/snapshot-vbd.sh %s" % 
                          os.path.basename(dst))
                log.debug('Performed VBD snapshot')

                tochild.write("done\n")
                tochild.flush()

            if line == "restart":
                global down_end

                log.debug("Restarting %d ...", dominfo.getDomid())
                dominfo.resumeDomain(downtime)

                # CoW timing
                downtime.append(time.time())

                tochild.write("done\n")
                tochild.flush()

        forkHelper(cmd, fd, saveInputHandler, False)

        # put qemu device model state
        if os.path.exists("/var/lib/xen/qemu-save.%d" % dominfo.getDomid()):
            os.remove("/var/lib/xen/qemu-save.%d" % dominfo.getDomid())
            write_exact(fd, QEMU_SIGNATURE, "could not write qemu signature")
            for buf in buf_list:
                if len(buf):
                    write_exact(fd, buf, "could not write device model state")
                else:
                    break
        try:
            dominfo.setName(domain_name)
        except VmError:
            # Ignore this.  The name conflict (hopefully) arises because we
            # are doing localhost migration; if we are doing a suspend of a
            # persistent VM, we need the rename, and don't expect the
            # conflict.  This needs more thought.
            pass

        # CoW timing
        checkpointtime.append(time.time())
        log.debug("[downtime] %s", downtime[2] - downtime[0])
        log.debug("[checkpoint_time] %s", 
				  checkpointtime[1] - checkpointtime[0])

    except Exception, exn:
        log.exception("Save failed on domain %s (%s) - resuming.", domain_name,
                      dominfo.getDomid())
        dominfo.resumeDomain([])
 
        try:
            dominfo.setName(domain_name)
        except:
            log.exception("Failed to reset the migrating domain's name")

        raise exn


def restore(xd, fd, dominfo = None, paused = False):
    signature = read_exact(fd, len(SIGNATURE),
        "not a valid guest state file: signature read")
    if signature != SIGNATURE:
        raise XendError("not a valid guest state file: found '%s'" %
                        signature)

    l = read_exact(fd, sizeof_int,
                   "not a valid guest state file: config size read")
    vmconfig_size = unpack("!i", l)[0]
    vmconfig_buf = read_exact(fd, vmconfig_size,
        "not a valid guest state file: config read")

    p = sxp.Parser()
    p.input(vmconfig_buf)
    if not p.ready:
        raise XendError("not a valid guest state file: config parse")

    vmconfig = p.get_val()

    if dominfo:
        dominfo.resume()
    else:
        dominfo = xd.restore_(vmconfig)

    store_port   = dominfo.getStorePort()
    console_port = dominfo.getConsolePort()

    assert store_port
    assert console_port

    # if hvm, pass mem size to calculate the store_mfn
    image_cfg = dominfo.info.get('image', {})
    is_hvm = dominfo.info.is_hvm()
    if is_hvm:
        apic = int(dominfo.info['platform'].get('apic', 0))
        pae  = int(dominfo.info['platform'].get('pae',  0))
        log.info("restore hvm domain %d, apic=%d, pae=%d",
                 dominfo.domid, apic, pae)
    else:
        apic = 0
        pae  = 0

    try:
        restore_image = image.create(dominfo, dominfo.info)
        memory = restore_image.getRequiredAvailableMemory(
            dominfo.info['memory_dynamic_max'] / 1024)
        maxmem = restore_image.getRequiredAvailableMemory(
            dominfo.info['memory_static_max'] / 1024)
        shadow = restore_image.getRequiredShadowMemory(
            dominfo.info['shadow_memory'] * 1024,
            dominfo.info['memory_static_max'] / 1024)

        log.debug("restore:shadow=0x%x, _static_max=0x%x, _static_min=0x%x, ",
                  dominfo.info['shadow_memory'],
                  dominfo.info['memory_static_max'],
                  dominfo.info['memory_static_min'])

        # Round shadow up to a multiple of a MiB, as shadow_mem_control
        # takes MiB and we must not round down and end up under-providing.
        shadow = ((shadow + 1023) / 1024) * 1024

        # set memory limit
        xc.domain_setmaxmem(dominfo.getDomid(), maxmem)

        balloon.free(memory + shadow)

        shadow_cur = xc.shadow_mem_control(dominfo.getDomid(), shadow / 1024)
        dominfo.info['shadow_memory'] = shadow_cur

        cmd = map(str, [xen.util.auxbin.pathTo(XC_RESTORE),
                        fd, dominfo.getDomid(),
                        store_port, console_port, int(is_hvm), pae, apic])
        log.debug("[xc_restore]: %s", string.join(cmd))

        handler = RestoreInputHandler()

        forkHelper(cmd, fd, handler.handler, True)

        # We don't want to pass this fd to any other children -- we 
        # might need to recover the disk space that backs it.
        try:
            flags = fcntl.fcntl(fd, fcntl.F_GETFD)
            flags |= fcntl.FD_CLOEXEC
            fcntl.fcntl(fd, fcntl.F_SETFD, flags)
        except:
            pass

        if handler.store_mfn is None:
            raise XendError('Could not read store MFN')

        if not is_hvm and handler.console_mfn is None:
            raise XendError('Could not read console MFN')        

        # get qemu state and create a tmp file for dm restore
        # Even PV guests may have QEMU stat, but its not currently
        # used so only bother with HVM currently.
        if is_hvm:
            qemu_signature = read_exact(fd, len(QEMU_SIGNATURE),
                                        "invalid device model signature read")
            if qemu_signature != QEMU_SIGNATURE:
                raise XendError("not a valid device model state: found '%s'" %
                                qemu_signature)
            qemu_fd = os.open("/var/lib/xen/qemu-save.%d" % dominfo.getDomid(),
                              os.O_WRONLY | os.O_CREAT | os.O_TRUNC)
            while True:
                buf = os.read(fd, dm_batch)
                if len(buf):
                    write_exact(qemu_fd, buf,
                                "could not write dm state to tmp file")
                else:
                    break
            os.close(qemu_fd)


        os.read(fd, 1)           # Wait for source to close connection
        
        dominfo.completeRestore(handler.store_mfn, handler.console_mfn)

        #
        # We shouldn't hold the domains_lock over a waitForDevices
        # As this function sometime gets called holding this lock,
        # we must release it and re-acquire it appropriately
        #
        from xen.xend import XendDomain

        lock = True;
        try:
            XendDomain.instance().domains_lock.release()
        except:
            lock = False;

        try:
            dominfo.waitForDevices() # Wait for backends to set up
        except Exception, exn:
            log.exception(exn)

        if lock:
            XendDomain.instance().domains_lock.acquire()

        if not paused:
            dominfo.unpause()

        return dominfo
    except:
        dominfo.destroy()
        raise


class RestoreInputHandler:
    def __init__(self):
        self.store_mfn = None
        self.console_mfn = None


    def handler(self, line, _):
        m = re.match(r"^(store-mfn) (\d+)$", line)
        if m:
            self.store_mfn = int(m.group(2))
        else:
            m = re.match(r"^(console-mfn) (\d+)$", line)
            if m:
                self.console_mfn = int(m.group(2))


def forkHelper(cmd, fd, inputHandler, closeToChild):
    child = xPopen3(cmd, True, -1, [fd, xc.handle()])

    if closeToChild:
        child.tochild.close()

    thread = threading.Thread(target = slurp, args = (child.childerr,))
    thread.start()

    try:
        try:
            while 1:
                line = child.fromchild.readline()
                if line == "":
                    break
                else:
                    line = line.rstrip()
                    log.debug('%s', line)
                    inputHandler(line, child.tochild)

        except IOError, exn:
            raise XendError('Error reading from child process for %s: %s' %
                            (cmd, exn))
    finally:
        child.fromchild.close()
        if not closeToChild:
            child.tochild.close()
        thread.join()
        child.childerr.close()
        status = child.wait()

    if status >> 8 == 127:
        raise XendError("%s failed: popen failed" % string.join(cmd))
    elif status != 0:
        raise XendError("%s failed" % string.join(cmd))


def slurp(infile):
    while 1:
        line = infile.readline()
        if line == "":
            break
        else:
            line = line.strip()
            m = re.match(r"^ERROR: (.*)", line)
            if m is None:
                log.info('%s', line)
            else:
                log.error('%s', m.group(1))
