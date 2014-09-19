#===========================================================================
# This library is free software; you can redistribute it and/or
# modify it under the terms of version 2.1 of the GNU Lesser General Public
# License as published by the Free Software Foundation.
#
# This library is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public
# License along with this library; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
#============================================================================
# Copyright (C) 2006-2007 XenSource Ltd
#============================================================================

import logging
import re
import time
import types

from xen.xend import sxp
from xen.xend import uuid
from xen.xend import XendOptions
from xen.xend import XendAPIStore
from xen.xend.XendError import VmError
from xen.xend.XendDevices import XendDevices
from xen.xend.PrettyPrint import prettyprintstring
from xen.xend.XendConstants import DOM_STATE_HALTED
from xen.xend.xenstore.xstransact import xstransact
from xen.xend.server.BlktapController import blktap_disk_types
from xen.xend.server.netif import randomMAC
from xen.util.blkif import blkdev_name_to_number, blkdev_uname_to_file
from xen.util import xsconstants
import xen.util.auxbin

log = logging.getLogger("xend.XendConfig")
log.setLevel(logging.WARN)


"""
XendConfig API

  XendConfig will try to mirror as closely the Xen API VM Struct
  with extra parameters for those options that are not supported.

"""

def reverse_dict(adict):
    """Return the reverse mapping of a dictionary."""
    return dict([(v, k) for k, v in adict.items()])

def bool0(v):
    return v != '0' and v != 'False' and bool(v)

# Recursively copy a data struct, scrubbing out VNC passwords.
# Will scrub any dict entry with a key of 'vncpasswd' or any
# 2-element list whose first member is 'vncpasswd'. It will
# also scrub a string matching '(vncpasswd XYZ)'. Everything
# else is no-op passthrough
def scrub_password(data):
    if type(data) == dict or type(data) == XendConfig:
        scrubbed = {}
        for key in data.keys():
            if key == "vncpasswd":
                scrubbed[key] = "XXXXXXXX"
            else:
                scrubbed[key] = scrub_password(data[key])
        return scrubbed
    elif type(data) == list:
        if len(data) == 2 and type(data[0]) == str and data[0] == 'vncpasswd':
            return ['vncpasswd', 'XXXXXXXX']
        else:
            scrubbed = []
            for entry in data:
                scrubbed.append(scrub_password(entry))
            return scrubbed
    elif type(data) == tuple:
        scrubbed = []
        for entry in data:
            scrubbed.append(scrub_password(entry))
        return tuple(scrubbed)
    elif type(data) == str:
        return re.sub(r'\(vncpasswd\s+[^\)]+\)','(vncpasswd XXXXXX)', data)
    else:
        return data

#
# CPU fields:
#
# VCPUs_max    -- the maximum number of vcpus that this domain may ever have.
#                 aka XendDomainInfo.getVCpuCount().
# vcpus        -- the legacy configuration name for above.
# max_vcpu_id  -- vcpus_number - 1.  This is given to us by Xen.
#
# cpus         -- the list of pCPUs available to each vCPU.
#
# vcpu_avail   -- a bitmap telling the guest domain whether it may use each of
#                 its VCPUs.  This is translated to
#                 <dompath>/cpu/<id>/availability = {online,offline} for use
#                 by the guest domain.
# VCPUs_live   -- the number of VCPUs currently up, as reported by Xen.  This
#                 is changed by changing vcpu_avail, and waiting for the
#                 domain to respond.
#


# Mapping from XendConfig configuration keys to the old
# legacy configuration keys that map directly.

XENAPI_CFG_TO_LEGACY_CFG = {
    'uuid': 'uuid',
    'VCPUs_max': 'vcpus',
    'cpus': 'cpus',
    'name_label': 'name',
    'actions_after_shutdown': 'on_poweroff',
    'actions_after_reboot': 'on_reboot',
    'actions_after_crash': 'on_crash', 
    'PV_bootloader': 'bootloader',
    'PV_bootloader_args': 'bootloader_args',
}

LEGACY_CFG_TO_XENAPI_CFG = reverse_dict(XENAPI_CFG_TO_LEGACY_CFG)

# Platform configuration keys.
XENAPI_PLATFORM_CFG = [ 'acpi', 'apic', 'boot', 'device_model', 'display', 
                        'fda', 'fdb', 'keymap', 'isa', 'localtime', 'monitor', 
                        'nographic', 'pae', 'rtc_timeoffset', 'serial', 'sdl',
                        'soundhw','stdvga', 'usb', 'usbdevice', 'vnc',
                        'vncconsole', 'vncdisplay', 'vnclisten', 'timer_mode',
                        'vncpasswd', 'vncunused', 'xauthority', 'pci', 'vhpt',
                        'guest_os_type' ]

# Xen API console 'other_config' keys.
XENAPI_CONSOLE_OTHER_CFG = ['vncunused', 'vncdisplay', 'vnclisten',
                            'vncpasswd', 'type', 'display', 'xauthority',
                            'keymap']

# List of XendConfig configuration keys that have no direct equivalent
# in the old world.

XENAPI_CFG_TYPES = {
    'uuid': str,
    'name_label': str,
    'name_description': str,
    'user_version': str,
    'is_a_template': bool0,
    'resident_on': str,
    'memory_static_min': int,  # note these are stored in bytes, not KB!
    'memory_static_max': int,
    'memory_dynamic_min': int,
    'memory_dynamic_max': int,
    'cpus': list,
    'vcpus_params': dict,
    'VCPUs_max': int,
    'VCPUs_at_startup': int,
    'VCPUs_live': int,
    'actions_after_shutdown': str,
    'actions_after_reboot': str,
    'actions_after_crash': str,
    'PV_bootloader': str,
    'PV_kernel': str,
    'PV_ramdisk': str,
    'PV_args': str,
    'PV_bootloader_args': str,
    'HVM_boot_policy': str,
    'HVM_boot_params': dict,
    'PCI_bus': str,
    'platform': dict,
    'tools_version': dict,
    'other_config': dict,
    'security_label': str,
    'pci': str,
}

# List of legacy configuration keys that have no equivalent in the
# Xen API, but are still stored in XendConfig.

LEGACY_UNSUPPORTED_BY_XENAPI_CFG = [
    # roundtripped (dynamic, unmodified)
    'shadow_memory',
    'vcpu_avail',
    'features',
    # read/write
    'on_xend_start',
    'on_xend_stop',
    # read-only
    'domid',
    'start_time',
    'cpu_time',
    'online_vcpus',
    # write-once
    'cpu',
    'cpus',
]

LEGACY_CFG_TYPES = {
    'uuid':          str,
    'name':          str,
    'vcpus':         int,
    'vcpu_avail':    long,
    'memory':        int,
    'shadow_memory': int,
    'maxmem':        int,
    'start_time':    float,
    'cpu_time':      float,
    'features':      str,
    'localtime':     int,
    'name':          str,
    'on_poweroff':   str,
    'on_reboot':     str,
    'on_crash':      str,
    'on_xend_stop':  str,
    'on_xend_start': str,
    'online_vcpus':  int,
    'rtc/timeoffset': str,
}

# Values that should be stored in xenstore's /vm/<uuid> that is used
# by Xend. Used in XendDomainInfo to restore running VM state from
# xenstore.
LEGACY_XENSTORE_VM_PARAMS = [
    'uuid',
    'name',
    'vcpus',
    'vcpu_avail',
    'memory',
    'shadow_memory',
    'maxmem',
    'start_time',
    'name',
    'on_poweroff',
    'on_crash',
    'on_reboot',
    'on_xend_start',
    'on_xend_stop',
]

##
## Config Choices
##

CONFIG_RESTART_MODES = ('restart', 'destroy', 'preserve', 'rename-restart')
CONFIG_OLD_DOM_STATES = ('running', 'blocked', 'paused', 'shutdown',
                         'crashed', 'dying')

class XendConfigError(VmError):
    def __str__(self):
        return 'Invalid Configuration: %s' % str(self.value)

##
## XendConfig Class (an extended dictionary)
##

class XendConfig(dict):
    """ The new Xend VM Configuration.

    Stores the configuration in xenapi compatible format but retains
    import and export functions for SXP.
    """
    def __init__(self, filename = None, sxp_obj = None,
                 xapi = None, dominfo = None):
        
        dict.__init__(self)
        self.update(self._defaults())

        if filename:
            try:
                sxp_obj = sxp.parse(open(filename,'r'))
                sxp_obj = sxp_obj[0]
            except IOError, e:
                raise XendConfigError("Unable to read file: %s" % filename)
        
        if sxp_obj:
            self._sxp_to_xapi(sxp_obj)
            self._sxp_to_xapi_unsupported(sxp_obj)
        elif xapi:
            self.update_with_xenapi_config(xapi)
        elif dominfo:
            # output from xc.domain_getinfo
            self._dominfo_to_xapi(dominfo, update_mem = True)

        log.debug('XendConfig.init: %s' % scrub_password(self))

        # validators go here
        self.validate()

    """ In time, we should enable this type checking addition. It is great
        also for tracking bugs and unintended writes to XendDomainInfo.info
    def __setitem__(self, key, value):
        type_conv = XENAPI_CFG_TYPES.get(key)
        if callable(type_conv):
            try:
                dict.__setitem__(self, key, type_conv(value))
            except (ValueError, TypeError):
                raise XendConfigError("Wrong type for configuration value " +
                                      "%s. Expected %s" %
                                      (key, type_conv.__name__))
        else:
            dict.__setitem__(self, key, value)
    """

    def _defaults(self):
        defaults = {
            'name_label': 'Domain-Unnamed',
            'actions_after_shutdown': 'destroy',
            'actions_after_reboot': 'restart',
            'actions_after_crash': 'restart',
            'actions_after_suspend': '',
            'is_a_template': False,
            'is_control_domain': False,
            'features': '',
            'PV_bootloader': '',
            'PV_kernel': '',
            'PV_ramdisk': '',
            'PV_args': '',
            'PV_bootloader_args': '',
            'HVM_boot_policy': '',
            'HVM_boot_params': {},
            'memory_static_min': 0,
            'memory_dynamic_min': 0,
            'shadow_memory': 0,
            'memory_static_max': 0,
            'memory_dynamic_max': 0,
            'devices': {},
            'on_xend_start': 'ignore',
            'on_xend_stop': 'ignore',
            'cpus': [],
            'VCPUs_max': 1,
            'VCPUs_live': 1,
            'VCPUs_at_startup': 1,
            'vcpus_params': {},
            'console_refs': [],
            'vif_refs': [],
            'vbd_refs': [],
            'vtpm_refs': [],
            'other_config': {},
            'platform': {}
        }
        
        return defaults

    #
    # Here we assume these values exist in the dict.
    # If they don't we have a bigger problem, lets not
    # try and 'fix it up' but acutually fix the cause ;-)
    #
    def _memory_sanity_check(self):
        log.trace("_memory_sanity_check memory_static_min: %s, "
                      "memory_static_max: %i, "
                      "memory_dynamic_min: %i, " 
                      "memory_dynamic_max: %i",
                      self["memory_static_min"],
                      self["memory_static_max"],
                      self["memory_dynamic_min"],
                      self["memory_dynamic_max"])
        
        if not self["memory_static_min"] <= self["memory_static_max"]:
            raise XendConfigError("memory_static_min must be less " \
                                  "than or equal to memory_static_max") 
        if not self["memory_static_min"] <= self["memory_dynamic_min"]:
            raise XendConfigError("memory_static_min must be less " \
                                  "than or equal to memory_dynamic_min")
        if not self["memory_dynamic_max"] <= self["memory_static_max"]:
            raise XendConfigError("memory_dynamic_max must be less " \
                                  "than or equal to memory_static_max")
        if not self["memory_dynamic_max"] > 0:
            raise XendConfigError("memory_dynamic_max must be greater " \
                                  "than zero")
        if not self["memory_static_max"] > 0:
            raise XendConfigError("memory_static_max must be greater " \
                                  "than zero")

    def _actions_sanity_check(self):
        for event in ['shutdown', 'reboot', 'crash']:
            if self['actions_after_' + event] not in CONFIG_RESTART_MODES:
                raise XendConfigError('Invalid event handling mode: ' +
                                      event)

    def _vcpus_sanity_check(self):
        if 'VCPUs_max' in self and 'vcpu_avail' not in self:
            self['vcpu_avail'] = (1 << self['VCPUs_max']) - 1

    def _uuid_sanity_check(self):
        """Make sure UUID is in proper string format with hyphens."""
        if 'uuid' not in self or not self['uuid']:
            self['uuid'] = uuid.createString()
        else:
            self['uuid'] = uuid.toString(uuid.fromString(self['uuid']))

    def _name_sanity_check(self):
        if 'name_label' not in self:
            self['name_label'] = 'Domain-' + self['uuid']

    def _platform_sanity_check(self):
        if 'keymap' not in self['platform'] and XendOptions.instance().get_keymap():
            self['platform']['keymap'] = XendOptions.instance().get_keymap()

        if self.is_hvm() or self.has_rfb():
            if 'device_model' not in self['platform']:
                self['platform']['device_model'] = xen.util.auxbin.pathTo("qemu-dm")

        if self.is_hvm():
            # Compatibility hack, can go away soon.
            if 'soundhw' not in self['platform'] and \
               self['platform'].get('enable_audio'):
                self['platform']['soundhw'] = 'sb16'

    def validate(self):
        self._uuid_sanity_check()
        self._name_sanity_check()
        self._memory_sanity_check()
        self._actions_sanity_check()
        self._vcpus_sanity_check()
        self._platform_sanity_check()

    def _dominfo_to_xapi(self, dominfo, update_mem = False):
        self['domid'] = dominfo['domid']
        self['online_vcpus'] = dominfo['online_vcpus']
        self['VCPUs_max'] = dominfo['max_vcpu_id'] + 1

        if update_mem:
            self['memory_dynamic_min'] = dominfo['mem_kb'] * 1024
            self['memory_dynamic_max'] = dominfo['mem_kb'] * 1024
            self['memory_static_min'] = 0
            self['memory_static_max'] = dominfo['maxmem_kb'] * 1024
            self._memory_sanity_check()

        self['cpu_time'] = dominfo['cpu_time']/1e9
        if dominfo.get('ssidref'):
            ssidref = int(dominfo.get('ssidref'))
            import xen.util.xsm.xsm as security
            self['security_label'] = security.ssidref2security_label(ssidref)

        self['shutdown_reason'] = dominfo['shutdown_reason']

        # parse state into Xen API states
        self['running'] = dominfo['running']
        self['crashed'] = dominfo['crashed']
        self['dying'] = dominfo['dying']
        self['shutdown'] = dominfo['shutdown']
        self['paused'] = dominfo['paused']
        self['blocked'] = dominfo['blocked']

        if 'name' in dominfo:
            self['name_label'] = dominfo['name']

        if 'handle' in dominfo:
            self['uuid'] = uuid.toString(dominfo['handle'])
            
    def _parse_sxp(self, sxp_cfg):
        """ Populate this XendConfig using the parsed SXP.

        @param sxp_cfg: Parsed SXP Configuration
        @type sxp_cfg: list of lists
        @rtype: dictionary
        @return: A dictionary containing the parsed options of the SXP.
        """
        cfg = {}

        for key, typ in XENAPI_CFG_TYPES.items():
            val = sxp.child_value(sxp_cfg, key)
            if val is not None:
                try:
                    cfg[key] = typ(val)
                except (ValueError, TypeError), e:
                    log.warn('Unable to convert type value for key: %s' % key)

        # Convert deprecated options to current equivalents.
        
        restart = sxp.child_value(sxp_cfg, 'restart')
        if restart:
            if restart == 'onreboot':
                cfg['on_poweroff'] = 'destroy'
                cfg['on_reboot'] = 'restart'
                cfg['on_crash'] = 'destroy'
            elif restart == 'always':
                for opt in ('on_poweroff', 'on_reboot', 'on_crash'):
                    cfg[opt] = 'restart'
            elif restart == 'never':
                for opt in ('on_poweroff', 'on_reboot', 'on_crash'):
                    cfg[opt] = 'never'                
            else:
                log.warn('Ignoring unrecognised value for deprecated option:'
                         'restart = \'%s\'', restart)

        # Handle memory, passed in as MiB

        if sxp.child_value(sxp_cfg, "memory") != None:
            cfg["memory"] = int(sxp.child_value(sxp_cfg, "memory"))
        if sxp.child_value(sxp_cfg, "maxmem") != None:
            cfg["maxmem"] = int(sxp.child_value(sxp_cfg, "maxmem"))
            
        # Convert scheduling parameters to vcpus_params
        if 'vcpus_params' not in cfg:
            cfg['vcpus_params'] = {}
        cfg["vcpus_params"]["weight"] = \
            int(sxp.child_value(sxp_cfg, "cpu_weight", 256))
        cfg["vcpus_params"]["cap"] = \
            int(sxp.child_value(sxp_cfg, "cpu_cap", 0))

        # Only extract options we know about.
        extract_keys = LEGACY_UNSUPPORTED_BY_XENAPI_CFG + \
                  XENAPI_CFG_TO_LEGACY_CFG.values()
        
        for key in extract_keys:
            val = sxp.child_value(sxp_cfg, key)
            if val != None:
                try:
                    cfg[key] = LEGACY_CFG_TYPES[key](val)
                except KeyError:
                    cfg[key] = val
                except (TypeError, ValueError), e:
                    log.warn("Unable to parse key %s: %s: %s" %
                             (key, str(val), e))

        if 'platform' not in cfg:
            cfg['platform'] = {}
        localtime = sxp.child_value(sxp_cfg, 'localtime')
        if localtime is not None:
            cfg['platform']['localtime'] = localtime

        # Compatibility hack -- can go soon.
        for key in XENAPI_PLATFORM_CFG:
            val = sxp.child_value(sxp_cfg, "platform_" + key, None)
            if val is not None:
                self['platform'][key] = val

        # Compatibility hack -- can go soon.
        boot_order = sxp.child_value(sxp_cfg, 'HVM_boot')
        if boot_order:
            cfg['HVM_boot_policy'] = 'BIOS order'
            cfg['HVM_boot_params'] = { 'order' : boot_order }

       
        # Parsing the device SXP's.
        cfg['devices'] = {}
        for dev in sxp.children(sxp_cfg, 'device'):
            config = sxp.child0(dev)
            dev_type = sxp.name(config)
            self.device_add(dev_type, cfg_sxp = config, target = cfg)

        # Extract missing data from configuration entries
        image_sxp = sxp.child_value(sxp_cfg, 'image', [])
        if image_sxp:
            image_vcpus = sxp.child_value(image_sxp, 'vcpus')
            if image_vcpus != None:
                try:
                    if 'VCPUs_max' not in cfg:
                        cfg['VCPUs_max'] = int(image_vcpus)
                    elif cfg['VCPUs_max'] != int(image_vcpus):
                        cfg['VCPUs_max'] = int(image_vcpus)
                        log.warn('Overriding vcpus from %d to %d using image'
                                 'vcpus value.', cfg['VCPUs_max'])
                except ValueError, e:
                    raise XendConfigError('integer expeceted: %s: %s' %
                                          image_sxp, e)

        # Deprecated cpu configuration
        if 'cpu' in cfg:
            if 'cpus' in cfg:
                cfg['cpus'] = "%s,%s" % (str(cfg['cpu']), cfg['cpus'])
            else:
                cfg['cpus'] = str(cfg['cpu'])

        # Convert 'cpus' to list of ints
        if 'cpus' in cfg:
            cpus = []
            if type(cfg['cpus']) == list:
                # If sxp_cfg was created from config.sxp,
                # the form of 'cpus' is list of string.
                # Convert 'cpus' to list of ints.
                #    ['1']         -> [1]
                #    ['0','2','3'] -> [0,2,3]
                try:
                    for c in cfg['cpus']:
                        cpus.append(int(c))
                    
                    cfg['cpus'] = cpus
                except ValueError, e:
                    raise XendConfigError('cpus = %s: %s' % (cfg['cpus'], e))
            else:
                # Convert 'cpus' string to list of ints
                # 'cpus' supports a list of ranges (0-3),
                # seperated by commas, and negation, (^1).  
                # Precedence is settled by order of the 
                # string:
                #    "0-3,^1"      -> [0,2,3]
                #    "0-3,^1,1"    -> [0,1,2,3]
                try:
                    for c in cfg['cpus'].split(','):
                        if c.find('-') != -1:             
                            (x, y) = c.split('-')
                            for i in range(int(x), int(y)+1):
                                cpus.append(int(i))
                        else:
                            # remove this element from the list 
                            if c[0] == '^':
                                cpus = [x for x in cpus if x != int(c[1:])]
                            else:
                                cpus.append(int(c))
                    
                    cfg['cpus'] = cpus
                except ValueError, e:
                    raise XendConfigError('cpus = %s: %s' % (cfg['cpus'], e))

        import xen.util.xsm.xsm as security
        if security.on():
            from xen.util.acmpolicy import ACM_LABEL_UNLABELED
            if not 'security' in cfg and sxp.child_value(sxp_cfg, 'security'):
                cfg['security'] = sxp.child_value(sxp_cfg, 'security')
            elif not cfg.get('security_label'):
                cfg['security'] = [['access_control',
                                     ['policy', security.get_active_policy_name() ],
                                     ['label', ACM_LABEL_UNLABELED ]]]

            if 'security' in cfg and not cfg.get('security_label'):
                secinfo = cfg['security']
                # The xm command sends a list formatted like this:
                # [['access_control', ['policy', 'xm-test'],['label', 'red']],
                #                     ['ssidref', 196611]]
                policy = ""
                label = ""
                for idx in range(0, len(secinfo)):
                    if secinfo[idx][0] == "access_control":
                        for aidx in range(1, len(secinfo[idx])):
                            if secinfo[idx][aidx][0] == "policy":
                                policy = secinfo[idx][aidx][1]
                            if secinfo[idx][aidx][0] == "label":
                                label  = secinfo[idx][aidx][1]
                cfg['security_label'] = \
                    security.set_security_label(policy, label)
                if not sxp.child_value(sxp_cfg, 'security_label'):
                    del cfg['security']

            sec_lab = cfg['security_label'].split(":")
            if len(sec_lab) != 3:
                raise XendConfigError("Badly formatted security label: %s"
                                      % cfg['security_label'])

        old_state = sxp.child_value(sxp_cfg, 'state')
        if old_state:
            for i in range(len(CONFIG_OLD_DOM_STATES)):
                cfg[CONFIG_OLD_DOM_STATES[i]] = int(old_state[i] != '-')

        return cfg
    

    def _sxp_to_xapi(self, sxp_cfg):
        """Read in an SXP Configuration object and
        populate at much of the Xen API with valid values.
        """
        log.debug('_sxp_to_xapi(%s)' % scrub_password(sxp_cfg))

        cfg = self._parse_sxp(sxp_cfg)

        for key, typ in XENAPI_CFG_TYPES.items():
            val = cfg.get(key)
            if val is not None:
                self[key] = typ(val)

        # Convert parameters that can be directly mapped from
        # the Legacy Config to Xen API Config
        
        for apikey, cfgkey in XENAPI_CFG_TO_LEGACY_CFG.items():
            try:
                type_conv = XENAPI_CFG_TYPES.get(apikey)
                if callable(type_conv):
                    self[apikey] = type_conv(cfg[cfgkey])
                else:
                    log.warn("Unconverted key: " + apikey)
                    self[apikey] = cfg[cfgkey]
            except KeyError:
                pass

        # Lets try and handle memory correctly

        MiB = 1024 * 1024

        if "memory" in cfg:
            self["memory_static_min"] = 0
            self["memory_static_max"] = int(cfg["memory"]) * MiB
            self["memory_dynamic_min"] = int(cfg["memory"]) * MiB
            self["memory_dynamic_max"] = int(cfg["memory"]) * MiB
            
            if "maxmem" in cfg:
                self["memory_static_max"] = int(cfg["maxmem"]) * MiB

        self._memory_sanity_check()

        def update_with(n, o):
            if not self.get(n):
                self[n] = cfg.get(o, '')

        update_with('PV_bootloader',      'bootloader')
        update_with('PV_bootloader_args', 'bootloader_args')

        image_sxp = sxp.child_value(sxp_cfg, 'image', [])
        if image_sxp:
            self.update_with_image_sxp(image_sxp)

        # Convert Legacy HVM parameters to Xen API configuration
        for key in XENAPI_PLATFORM_CFG:
            if key in cfg:
                self['platform'][key] = cfg[key]

        # set device references in the configuration
        self['devices'] = cfg.get('devices', {})
        self['console_refs'] = cfg.get('console_refs', [])
        self['vif_refs'] = cfg.get('vif_refs', [])
        self['vbd_refs'] = cfg.get('vbd_refs', [])
        self['vtpm_refs'] = cfg.get('vtpm_refs', [])

        # coalesce hvm vnc frame buffer with vfb config
        if self.is_hvm() and int(self['platform'].get('vnc', 0)) != 0:
            # add vfb device if it isn't there already
            if not self.has_rfb():
                dev_config = ['vfb']
                dev_config.append(['type', 'vnc'])
                # copy VNC related params from platform config to vfb dev conf
                for key in ['vncpasswd', 'vncunused', 'vncdisplay',
                            'vnclisten']:
                    if key in self['platform']:
                        dev_config.append([key, self['platform'][key]])

                self.device_add('vfb', cfg_sxp = dev_config)


    def has_rfb(self):
        for console_uuid in self['console_refs']:
            if self['devices'][console_uuid][1].get('protocol') == 'rfb':
                return True
            if self['devices'][console_uuid][0] == 'vfb':
                return True
        return False

    def _sxp_to_xapi_unsupported(self, sxp_cfg):
        """Read in an SXP configuration object and populate
        values are that not related directly supported in
        the Xen API.
        """

        log.debug('_sxp_to_xapi_unsupported(%s)' % scrub_password(sxp_cfg))

        # Parse and convert parameters used to configure
        # the image (as well as HVM images)
        image_sxp = sxp.child_value(sxp_cfg, 'image', [])
        if image_sxp:
            image_type = sxp.name(image_sxp)
            if image_type != 'hvm' and image_type != 'linux':
                self['platform']['image_type'] = image_type
            
            for key in XENAPI_PLATFORM_CFG:
                val = sxp.child_value(image_sxp, key, None)
                if val is not None and val != '':
                    self['platform'][key] = val
            
            notes = sxp.children(image_sxp, 'notes')
            if notes:
                self['notes'] = self.notes_from_sxp(notes[0])

            self._hvm_boot_params_from_sxp(image_sxp)

        # extract backend value
                    
        backend = []
        for c in sxp.children(sxp_cfg, 'backend'):
            backend.append(sxp.name(sxp.child0(c)))
        if backend:
            self['backend'] = backend

        # Parse and convert other Non Xen API parameters.
        def _set_cfg_if_exists(sxp_arg):
            val = sxp.child_value(sxp_cfg, sxp_arg)
            if val != None:
                if LEGACY_CFG_TYPES.get(sxp_arg):
                    self[sxp_arg] = LEGACY_CFG_TYPES[sxp_arg](val)
                else:
                    self[sxp_arg] = val

        _set_cfg_if_exists('shadow_memory')
        _set_cfg_if_exists('features')
        _set_cfg_if_exists('on_xend_stop')
        _set_cfg_if_exists('on_xend_start')
        _set_cfg_if_exists('vcpu_avail')
        
        # Parse and store runtime configuration 
        _set_cfg_if_exists('start_time')
        _set_cfg_if_exists('cpu_time')
        _set_cfg_if_exists('shutdown_reason')
        _set_cfg_if_exists('up_time')
        _set_cfg_if_exists('status') # TODO, deprecated  

    def _get_old_state_string(self):
        """Returns the old xm state string.
        @rtype: string
        @return: old state string
        """
        state_string = ''
        for state_name in CONFIG_OLD_DOM_STATES:
            on_off = self.get(state_name, 0)
            if on_off:
                state_string += state_name[0]
            else:
                state_string += '-'

        return state_string


    def update_config(self, dominfo):
        """Update configuration with the output from xc.domain_getinfo().

        @param dominfo: Domain information via xc.domain_getinfo()
        @type dominfo: dict
        """
        self._dominfo_to_xapi(dominfo)
        self.validate()

    def update_with_xenapi_config(self, xapi):
        """Update configuration with a Xen API VM struct

        @param xapi: Xen API VM Struct
        @type xapi: dict
        """

        log.debug('update_with_xenapi_config: %s' % scrub_password(xapi))

        for key, val in xapi.items():
            type_conv = XENAPI_CFG_TYPES.get(key)
            if type_conv is None:
                key = key.lower()
                type_conv = XENAPI_CFG_TYPES.get(key)
            if callable(type_conv):
                self[key] = type_conv(val)
            else:
                self[key] = val
                
        self['vcpus_params']['weight'] = \
            int(self['vcpus_params'].get('weight', 256))
        self['vcpus_params']['cap'] = int(self['vcpus_params'].get('cap', 0))

    def to_sxp(self, domain = None, ignore_devices = False, ignore = [],
               legacy_only = True):
        """ Get SXP representation of this config object.

        Incompat: removed store_mfn, console_mfn

        @keyword domain: (optional) XendDomainInfo to get extra information
                         from such as domid and running devices.
        @type    domain: XendDomainInfo
        @keyword ignore: (optional) list of 'keys' that we do not want
                         to export.
        @type    ignore: list of strings
        @rtype: list of list (SXP representation)
        """
        sxpr = ['domain']

        # TODO: domid/dom is the same thing but called differently
        #       depending if it is from xenstore or sxpr.

        if domain.getDomid() is not None:
            sxpr.append(['domid', domain.getDomid()])

        if not legacy_only:
            for name, typ in XENAPI_CFG_TYPES.items():
                if name in self and self[name] not in (None, []):
                    if typ == dict:
                        s = self[name].items()
                    elif typ == list:
                        s = self[name]
                    else:
                        s = str(self[name])
                    sxpr.append([name, s])

        for xenapi, legacy in XENAPI_CFG_TO_LEGACY_CFG.items():
            if legacy in ('cpus'): # skip this
                continue
            if self.has_key(xenapi) and self[xenapi] not in (None, []):
                if type(self[xenapi]) == bool:
                    # convert booleans to ints before making an sxp item
                    sxpr.append([legacy, int(self[xenapi])])
                else:
                    sxpr.append([legacy, self[xenapi]])

        MiB = 1024*1024

        sxpr.append(["maxmem", int(self["memory_static_max"])/MiB])
        sxpr.append(["memory", int(self["memory_dynamic_max"])/MiB])

        for legacy in LEGACY_UNSUPPORTED_BY_XENAPI_CFG:
            if legacy in ('domid', 'uuid', 'cpus'): # skip these
                continue
            if self.has_key(legacy) and self[legacy] not in (None, []):
                sxpr.append([legacy, self[legacy]])

        if self.has_key('security_label'):
            sxpr.append(['security_label', self['security_label']])

        sxpr.append(['image', self.image_sxpr()])
        sxpr.append(['status', domain._stateGet()])

        if domain.getDomid() is not None:
            sxpr.append(['state', self._get_old_state_string()])

        if domain:
            if domain.store_mfn:
                sxpr.append(['store_mfn', domain.store_mfn])
            if domain.console_mfn:
                sxpr.append(['console_mfn', domain.console_mfn])


        # Marshall devices (running or from configuration)
        if not ignore_devices:
            txn = xstransact()
            try:
                for cls in XendDevices.valid_devices():
                    found = False
                
                    # figure if there is a dev controller is valid and running
                    if domain and domain.getDomid() != None:
                        try:
                            controller = domain.getDeviceController(cls)
                            configs = controller.configurations(txn)
                            for config in configs:
                                if sxp.name(config) in ('vbd', 'tap'):
                                    # The bootable flag is never written to the
                                    # store as part of the device config.
                                    dev_uuid = sxp.child_value(config, 'uuid')
                                    dev_type, dev_cfg = self['devices'][dev_uuid]
                                    is_bootable = dev_cfg.get('bootable', 0)
                                    config.append(['bootable', int(is_bootable)])
                                    config.append(['VDI', dev_cfg.get('VDI', '')])

                                sxpr.append(['device', config])

                            found = True
                        except:
                            log.exception("dumping sxp from device controllers")
                            pass
                    
                    # if we didn't find that device, check the existing config
                    # for a device in the same class
                    if not found:
                        for dev_type, dev_info in self.all_devices_sxpr():
                            if dev_type == cls:
                                sxpr.append(['device', dev_info])

                txn.commit()
            except:
                txn.abort()
                raise

        return sxpr    
    
    def _blkdev_name_to_number(self, dev):
        if 'ioemu:' in dev:
            _, dev = dev.split(':', 1)
        try:
            dev, _ = dev.split(':', 1)
        except ValueError:
            pass
        
        try:
            devid = int(dev)
        except ValueError:
            # devid is not a number but a string containing either device
            # name (e.g. xvda) or device_type/device_id (e.g. vbd/51728)
            dev2 = type(dev) is str and dev.split('/')[-1] or None
            if dev2 == None:
                log.debug("Could not check the device %s", dev)
                return None
            try:
                devid = int(dev2)
            except ValueError:
                devid = blkdev_name_to_number(dev2)
                if devid == None:
                    log.debug("The device %s is not device name", dev2)
                    return None
        return devid
    
    def device_duplicate_check(self, dev_type, dev_info, defined_config):
        defined_devices_sxpr = self.all_devices_sxpr(target = defined_config)
        
        if dev_type == 'vbd' or dev_type == 'tap':
            dev_uname = dev_info.get('uname')
            blkdev_name = dev_info.get('dev')
            devid = self._blkdev_name_to_number(blkdev_name)
            if devid == None or dev_uname == None:
                return
            
            for o_dev_type, o_dev_info in defined_devices_sxpr:
                if o_dev_type == 'vbd' or o_dev_type == 'tap':
                    blkdev_file = blkdev_uname_to_file(dev_uname)
                    o_dev_uname = sxp.child_value(o_dev_info, 'uname')

                    # Ignore a null cdrom definition string
                    if o_dev_uname is None:
                        continue 

                    o_blkdev_file = blkdev_uname_to_file(o_dev_uname)
                    if blkdev_file == o_blkdev_file:
                        raise XendConfigError('The file "%s" is already used' %
                                              blkdev_file)
                    o_blkdev_name = sxp.child_value(o_dev_info, 'dev')
                    o_devid = self._blkdev_name_to_number(o_blkdev_name)
                    if o_devid != None and devid == o_devid:
                        raise XendConfigError('The device "%s" is already defined' %
                                              blkdev_name)
                    
        elif dev_type == 'vif':
            dev_mac = dev_info.get('mac')
            
            for o_dev_type, o_dev_info in defined_devices_sxpr:
                if dev_type == o_dev_type:
                    if dev_mac.lower() == sxp.child_value(o_dev_info, 'mac').lower():
                        raise XendConfigError('The mac "%s" is already defined' %
                                              dev_mac)
    
    def device_add(self, dev_type, cfg_sxp = None, cfg_xenapi = None,
                   target = None):
        """Add a device configuration in SXP format or XenAPI struct format.

        For SXP, it could be either:

        [device, [vbd, [uname ...]]

        or:

        [vbd, [uname ..]]

        @type cfg_sxp: list of lists (parsed sxp object)
        @param cfg_sxp: SXP configuration object
        @type cfg_xenapi: dict
        @param cfg_xenapi: A device configuration from Xen API (eg. vbd,vif)
        @param target: write device information to
        @type target: None or a dictionary
        @rtype: string
        @return: Assigned UUID of the device.
        """
        if target == None:
            target = self
        
        if dev_type not in XendDevices.valid_devices():
            raise XendConfigError("XendConfig: %s not a valid device type" %
                            dev_type)

        if cfg_sxp == None and cfg_xenapi == None:
            raise XendConfigError("XendConfig: device_add requires some "
                                  "config.")

        #if cfg_sxp:
        #    log.debug("XendConfig.device_add: %s" % str(cfg_sxp))
        #if cfg_xenapi:
        #    log.debug("XendConfig.device_add: %s" % str(cfg_xenapi))

        if cfg_sxp:
            if sxp.child0(cfg_sxp) == 'device':
                config = sxp.child0(cfg_sxp)
            else:
                config = cfg_sxp

            dev_type = sxp.name(config)
            dev_info = {}

            # Parsing the device SXP's. In most cases, the SXP looks
            # like this:
            #
            # [device, [vif, [mac, xx:xx:xx:xx:xx:xx], [ip 1.3.4.5]]]
            #
            # However, for PCI devices it looks like this:
            #
            # [device, [pci, [dev, [domain, 0], [bus, 0], [slot, 1]]]]
            #
            # It seems the reasoning for this difference is because
            # pciif.py needs all the PCI device configurations at
            # the same time when creating the devices.
            #
            # To further complicate matters, Xen 2.0 configuration format
            # uses the following for pci device configuration:
            #
            # [device, [pci, [domain, 0], [bus, 0], [dev, 1], [func, 2]]]

            if dev_type == 'pci':
                pci_devs_uuid = sxp.child_value(config, 'uuid',
                                                uuid.createString())
                pci_devs = []
                for pci_dev in sxp.children(config, 'dev'):
                    pci_dev_info = {}
                    for opt_val in pci_dev[1:]:
                        try:
                            opt, val = opt_val
                            pci_dev_info[opt] = val
                        except TypeError:
                            pass
                    pci_devs.append(pci_dev_info)
                target['devices'][pci_devs_uuid] = (dev_type,
                                                    {'devs': pci_devs,
                                                     'uuid': pci_devs_uuid})

                log.debug("XendConfig: reading device: %s" % pci_devs)
                return pci_devs_uuid

            for opt_val in config[1:]:
                try:
                    opt, val = opt_val
                    dev_info[opt] = val
                except (TypeError, ValueError): # unpack error
                    pass

            if dev_type == 'vbd':
                dev_info['bootable'] = 0
                if dev_info.get('dev', '').startswith('ioemu:'):
                    dev_info['driver'] = 'ioemu'
                else:
                    dev_info['driver'] = 'paravirtualised'

            if dev_type == 'tap':
                if dev_info['uname'].split(':')[1] not in blktap_disk_types:
                    raise XendConfigError("tap:%s not a valid disk type" %
                                    dev_info['uname'].split(':')[1])

            if dev_type == 'vif':
                if not dev_info.get('mac'):
                    dev_info['mac'] = randomMAC()

            self.device_duplicate_check(dev_type, dev_info, target)

            if dev_type == 'vif':
                if dev_info.get('policy') and dev_info.get('label'):
                    dev_info['security_label'] = "%s:%s:%s" % \
                        (xsconstants.ACM_POLICY_ID,
                         dev_info['policy'],dev_info['label'])

            # create uuid if it doesn't exist
            dev_uuid = dev_info.get('uuid', None)
            if not dev_uuid:
                dev_uuid = uuid.createString()
            dev_info['uuid'] = dev_uuid

            # store dev references by uuid for certain device types
            target['devices'][dev_uuid] = (dev_type, dev_info)
            if dev_type in ('vif', 'vbd', 'vtpm'):
                param = '%s_refs' % dev_type
                if param not in target:
                    target[param] = []
                if dev_uuid not in target[param]:
                    if dev_type == 'vbd':
                        # Compat hack -- mark first disk bootable
                        dev_info['bootable'] = int(not target[param])
                    target[param].append(dev_uuid)
            elif dev_type == 'tap':
                if 'vbd_refs' not in target:
                    target['vbd_refs'] = []
                if dev_uuid not in target['vbd_refs']:
                    # Compat hack -- mark first disk bootable
                    dev_info['bootable'] = int(not target['vbd_refs'])
                    target['vbd_refs'].append(dev_uuid)
                    
            elif dev_type == 'vfb':
                # Populate other config with aux data that is associated
                # with vfb

                other_config = {}
                for key in XENAPI_CONSOLE_OTHER_CFG:
                    if key in dev_info:
                        other_config[key] = dev_info[key]
                target['devices'][dev_uuid][1]['other_config'] =  other_config
                
                
                if 'console_refs' not in target:
                    target['console_refs'] = []

                # Treat VFB devices as console devices so they are found
                # through Xen API
                if dev_uuid not in target['console_refs']:
                    target['console_refs'].append(dev_uuid)

            elif dev_type == 'console':
                if 'console_refs' not in target:
                    target['console_refs'] = []
                if dev_uuid not in target['console_refs']:
                    target['console_refs'].append(dev_uuid)
                    
            log.debug("XendConfig: reading device: %s" % scrub_password(dev_info))
            return dev_uuid

        if cfg_xenapi:
            dev_info = {}
            dev_uuid = ''
            if dev_type == 'vif':
                dev_info['mac'] = cfg_xenapi.get('MAC')
                if not dev_info['mac']:
                    dev_info['mac'] = randomMAC()
                # vifname is the name on the guest, not dom0
                # TODO: we don't have the ability to find that out or
                #       change it from dom0
                #if cfg_xenapi.get('device'):  # don't add if blank
                #    dev_info['vifname'] = cfg_xenapi.get('device')
                if cfg_xenapi.get('type'):
                    dev_info['type'] = cfg_xenapi.get('type')
                if cfg_xenapi.get('name'):
                    dev_info['name'] = cfg_xenapi.get('name')
                if cfg_xenapi.get('network'):
                    network = XendAPIStore.get(
                        cfg_xenapi.get('network'), 'network')
                    dev_info['bridge'] = network.get_name_label()

                if cfg_xenapi.get('security_label'):
                    dev_info['security_label'] = \
                         cfg_xenapi.get('security_label')
                
                dev_uuid = cfg_xenapi.get('uuid', None)
                if not dev_uuid:
                    dev_uuid = uuid.createString()
                dev_info['uuid'] = dev_uuid
                target['devices'][dev_uuid] = (dev_type, dev_info)
                target['vif_refs'].append(dev_uuid)
            
            elif dev_type in ('vbd', 'tap'):
                dev_info['type'] = cfg_xenapi.get('type', 'Disk')
                if dev_info['type'] == 'CD':
                    old_vbd_type = 'cdrom'
                else:
                    old_vbd_type = 'disk'
                    
                dev_info['uname'] = cfg_xenapi.get('image', '')
                dev_info['dev'] = '%s:%s' % (cfg_xenapi.get('device'),
                                             old_vbd_type)
                dev_info['bootable'] = int(cfg_xenapi.get('bootable', 0))
                dev_info['driver'] = cfg_xenapi.get('driver', '')
                dev_info['VDI'] = cfg_xenapi.get('VDI', '')
                    
                if cfg_xenapi.get('mode') == 'RW':
                    dev_info['mode'] = 'w'
                else:
                    dev_info['mode'] = 'r'

                dev_uuid = cfg_xenapi.get('uuid', None)
                if not dev_uuid:
                    dev_uuid = uuid.createString()
                dev_info['uuid'] = dev_uuid
                target['devices'][dev_uuid] = (dev_type, dev_info)
                target['vbd_refs'].append(dev_uuid)                

            elif dev_type == 'vtpm':
                if cfg_xenapi.get('type'):
                    dev_info['type'] = cfg_xenapi.get('type')

                dev_uuid = cfg_xenapi.get('uuid', None)
                if not dev_uuid:
                    dev_uuid = uuid.createString()
                dev_info['uuid'] = dev_uuid
                dev_info['other_config'] = cfg_xenapi.get('other_config', {})
                target['devices'][dev_uuid] = (dev_type, dev_info)
                target['vtpm_refs'].append(dev_uuid)

            elif dev_type == 'console':
                dev_uuid = cfg_xenapi.get('uuid', None)
                if not dev_uuid:
                    dev_uuid = uuid.createString()
                dev_info['uuid'] = dev_uuid
                dev_info['protocol'] = cfg_xenapi.get('protocol', 'rfb')
                dev_info['other_config'] = cfg_xenapi.get('other_config', {})
                if dev_info['protocol'] == 'rfb':
                    # collapse other config into devinfo for things
                    # such as vncpasswd, vncunused, etc.                    
                    dev_info.update(cfg_xenapi.get('other_config', {}))
                    dev_info['type'] = 'vnc'                        
                    target['devices'][dev_uuid] = ('vfb', dev_info)
                    target['console_refs'].append(dev_uuid)

                    # Finally, if we are a pvfb, we need to make a vkbd
                    # as well that is not really exposed to Xen API
                    vkbd_uuid = uuid.createString()
                    target['devices'][vkbd_uuid] = ('vkbd', {})
                    
                elif dev_info['protocol'] == 'vt100':
                    # if someone tries to create a VT100 console
                    # via the Xen API, we'll have to ignore it
                    # because we create one automatically in
                    # XendDomainInfo._update_consoles
                    raise XendConfigError('Creating vt100 consoles via '
                                          'Xen API is unsupported')

            return dev_uuid

        # no valid device to add
        return ''

    def phantom_device_add(self, dev_type, cfg_xenapi = None,
                   target = None):
        """Add a phantom tap device configuration in XenAPI struct format.
        """

        if target == None:
            target = self
        
        if dev_type not in XendDevices.valid_devices() and \
           dev_type not in XendDevices.pseudo_devices():        
            raise XendConfigError("XendConfig: %s not a valid device type" %
                            dev_type)

        if cfg_xenapi == None:
            raise XendConfigError("XendConfig: device_add requires some "
                                  "config.")

        if cfg_xenapi:
            log.debug("XendConfig.phantom_device_add: %s" % str(cfg_xenapi))
 
        if cfg_xenapi:
            dev_info = {}            
            if dev_type in ('vbd', 'tap'):
                if dev_type == 'vbd':
                    dev_info['uname'] = cfg_xenapi.get('image', '')
                    dev_info['dev'] = '%s:disk' % cfg_xenapi.get('device')
                elif dev_type == 'tap':
                    if cfg_xenapi.get('image').find('tap:') == -1:
                        dev_info['uname'] = 'tap:qcow:%s' % cfg_xenapi.get('image')
                    dev_info['dev'] =  '/dev/%s' % cfg_xenapi.get('device')
                    dev_info['uname'] = cfg_xenapi.get('image')
                dev_info['mode'] = cfg_xenapi.get('mode')
                dev_info['backend'] = '0'
                dev_uuid = cfg_xenapi.get('uuid', uuid.createString())
                dev_info['uuid'] = dev_uuid
                self['devices'][dev_uuid] = (dev_type, dev_info)
                self['vbd_refs'].append(dev_uuid)
                return dev_uuid

        return ''

    def console_add(self, protocol, location, other_config = {}):
        dev_uuid = uuid.createString()
        if protocol == 'vt100':
            dev_info = {
                'uuid': dev_uuid,
                'protocol': protocol,
                'location': location,
                'other_config': other_config,
            }

            if 'devices' not in self:
                self['devices'] = {}
            
            self['devices'][dev_uuid] = ('console', dev_info)
            self['console_refs'].append(dev_uuid)
            return dev_info

        return {}

    def console_update(self, console_uuid, key, value):
        for dev_uuid, (dev_type, dev_info) in self['devices'].items():
            if dev_uuid == console_uuid:
                dev_info[key] = value
                # collapse other_config into dev_info for things
                # such as vncpasswd, vncunused, etc.
                if key == 'other_config':
                    for k in XENAPI_CONSOLE_OTHER_CFG:
                        if k in dev_info and k not in value:
                            del dev_info[k]
                    dev_info.update(value)
                break

    def console_get_all(self, protocol):
        if protocol == 'vt100':
            consoles = [dinfo for dtype, dinfo in self['devices'].values()
                        if dtype == 'console']
            return [c for c in consoles if c.get('protocol') == protocol]

        elif protocol == 'rfb':
            vfbs = [dinfo for dtype, dinfo in self['devices'].values()
                   if dtype == 'vfb']

            # move all non-console key values to other_config before
            # returning console config
            valid_keys = ['uuid', 'location']
            for vfb in vfbs:
                other_config = {}
                for key, val in vfb.items():
                    if key not in valid_keys:
                        other_config[key] = vfb[key]
                    del vfb[key]
                vfb['other_config'] = other_config
                vfb['protocol'] = 'rfb'
                        
            return vfbs

        else:
            return []

    def device_update(self, dev_uuid, cfg_sxp = [], cfg_xenapi = {}):
        """Update an existing device with the new configuration.

        @rtype: boolean
        @return: Returns True if succesfully found and updated a device conf
        """
        if dev_uuid in self['devices'] and cfg_sxp:
            if sxp.child0(cfg_sxp) == 'device':            
                config = sxp.child0(cfg_sxp)
            else:
                config = cfg_sxp

            dev_type, dev_info = self['devices'][dev_uuid]
            for opt_val in config[1:]:
                try:
                    opt, val = opt_val
                    dev_info[opt] = val
                except (TypeError, ValueError):
                    pass # no value for this config option

            self['devices'][dev_uuid] = (dev_type, dev_info)
            return True
        
        elif dev_uuid in self['devices'] and cfg_xenapi:
            dev_type, dev_info = self['devices'][dev_uuid]
            for key, val in cfg_xenapi.items():
                dev_info[key] = val
            self['devices'][dev_uuid] = (dev_type, dev_info)

        return False


    def device_sxpr(self, dev_uuid = None, dev_type = None, dev_info = None, target = None):
        """Get Device SXPR by either giving the device UUID or (type, config).

        @rtype: list of lists
        @return: device config sxpr
        """
        sxpr = []

        if target == None:
            target = self

        if dev_uuid != None and dev_uuid in target['devices']:
            dev_type, dev_info = target['devices'][dev_uuid]

        if dev_type == None or dev_info == None:
            raise XendConfigError("Required either UUID or device type and "
                                  "configuration dictionary.")
            
        sxpr.append(dev_type)
        if dev_type in ('console', 'vfb'):
            config = [(opt, val) for opt, val in dev_info.items()
                      if opt != 'other_config']
        else:
            config = [(opt, val) for opt, val in dev_info.items()]
            
        sxpr += config

        return sxpr

    def ordered_device_refs(self, target = None):
        result = []

        if target == None:
            target = self

        # vkbd devices *must* be before vfb devices, otherwise
        # there is a race condition when setting up devices
        # where the daemon spawned for the vfb may write stuff
        # into xenstore vkbd backend, before DevController has
        # setup permissions on the vkbd backend path. This race
        # results in domain creation failing with 'device already
        # connected' messages
        result.extend([u for u in target['devices'].keys() if target['devices'][u][0] == 'vkbd'])

        result.extend(target.get('console_refs', []) +
                      target.get('vbd_refs', []) +
                      target.get('vif_refs', []) +
                      target.get('vtpm_refs', []))

        result.extend([u for u in target['devices'].keys() if u not in result])
        return result

    def all_devices_sxpr(self, target = None):
        """Returns the SXPR for all devices in the current configuration."""
        sxprs = []
        pci_devs = []

        if target == None:
            target = self

        if 'devices' not in target:
            return sxprs
        
        ordered_refs = self.ordered_device_refs(target = target)
        for dev_uuid in ordered_refs:
            dev_type, dev_info = target['devices'][dev_uuid]
            if dev_type == 'pci': # special case for pci devices
                sxpr = ['pci', ['uuid', dev_info['uuid']]]
                for pci_dev_info in dev_info['devs']:
                    pci_dev_sxpr = ['dev']
                    for opt, val in pci_dev_info.items():
                        pci_dev_sxpr.append([opt, val])
                    sxpr.append(pci_dev_sxpr)
                sxprs.append((dev_type, sxpr))
            else:
                sxpr = self.device_sxpr(dev_type = dev_type,
                                        dev_info = dev_info,
                                        target   = target)
                sxprs.append((dev_type, sxpr))

        return sxprs

    def image_sxpr(self):
        """Returns a backwards compatible image SXP expression that is
        used in xenstore's /vm/<uuid>/image value and xm list."""
        image = [self.image_type()]
        if self.has_key('PV_kernel'):
            image.append(['kernel', self['PV_kernel']])
        if self.has_key('PV_ramdisk') and self['PV_ramdisk']:
            image.append(['ramdisk', self['PV_ramdisk']])
        if self.has_key('PV_args') and self['PV_args']:
            image.append(['args', self['PV_args']])

        for key in XENAPI_PLATFORM_CFG:
            if key in self['platform']:
                image.append([key, self['platform'][key]])

        if 'notes' in self:
            image.append(self.notes_sxp(self['notes']))

        return image

    def update_with_image_sxp(self, image_sxp, bootloader = False):
        # Convert Legacy "image" config to Xen API PV_*
        # configuration
        log.debug("update_with_image_sxp(%s)" % scrub_password(image_sxp))

        # user-specified args must come last: previous releases did this and
        # some domU kernels rely upon the ordering.
        kernel_args = sxp.child_value(image_sxp, 'args', '')

        # attempt to extract extra arguments from SXP config
        arg_ip = sxp.child_value(image_sxp, 'ip')
        if arg_ip and not re.search(r'ip=[^ ]+', kernel_args):
            kernel_args = 'ip=%s ' % arg_ip + kernel_args
        arg_root = sxp.child_value(image_sxp, 'root')
        if arg_root and not re.search(r'root=', kernel_args):
            kernel_args = 'root=%s ' % arg_root + kernel_args

        if bootloader:
            self['_temp_using_bootloader'] = '1'
            self['_temp_kernel'] = sxp.child_value(image_sxp, 'kernel','')
            self['_temp_ramdisk'] = sxp.child_value(image_sxp, 'ramdisk','')
            self['_temp_args'] = kernel_args
        else:
            self['PV_kernel'] = sxp.child_value(image_sxp, 'kernel','')
            self['PV_ramdisk'] = sxp.child_value(image_sxp, 'ramdisk','')
            self['PV_args'] = kernel_args

        for key in XENAPI_PLATFORM_CFG:
            val = sxp.child_value(image_sxp, key, None)
            if val is not None and val != '':
                self['platform'][key] = val

        notes = sxp.children(image_sxp, 'notes')
        if notes:
            self['notes'] = self.notes_from_sxp(notes[0])

        self._hvm_boot_params_from_sxp(image_sxp)

    def set_notes(self, notes):
        'Add parsed elfnotes to image'
        self['notes'] = notes

    def get_notes(self):
        try:
            return self['notes'] or {}
        except KeyError:
            return {}

    def notes_from_sxp(self, nsxp):
        notes = {}
        for note in sxp.children(nsxp):
            notes[note[0]] = note[1]
        return notes

    def notes_sxp(self, notes):
        nsxp = ['notes']
        for k, v in notes.iteritems():
            nsxp.append([k, str(v)])
        return nsxp
        
    def _hvm_boot_params_from_sxp(self, image_sxp):
        boot = sxp.child_value(image_sxp, 'boot', None)
        if boot is not None:
            self['HVM_boot_policy'] = 'BIOS order'
            self['HVM_boot_params'] = { 'order' : boot }

    def is_hvm(self):
        return self['HVM_boot_policy'] != ''

    def image_type(self):
        stored_type = self['platform'].get('image_type')
        return stored_type or (self.is_hvm() and 'hvm' or 'linux')
