/* This file is automatically generated.  Do not edit. */
   S_(SECCLASS_XEN, XEN__SCHEDULER, "scheduler")
   S_(SECCLASS_XEN, XEN__SETTIME, "settime")
   S_(SECCLASS_XEN, XEN__TBUFCONTROL, "tbufcontrol")
   S_(SECCLASS_XEN, XEN__READCONSOLE, "readconsole")
   S_(SECCLASS_XEN, XEN__CLEARCONSOLE, "clearconsole")
   S_(SECCLASS_XEN, XEN__PERFCONTROL, "perfcontrol")
   S_(SECCLASS_XEN, XEN__MTRR_ADD, "mtrr_add")
   S_(SECCLASS_XEN, XEN__MTRR_DEL, "mtrr_del")
   S_(SECCLASS_XEN, XEN__MTRR_READ, "mtrr_read")
   S_(SECCLASS_XEN, XEN__MICROCODE, "microcode")
   S_(SECCLASS_XEN, XEN__PHYSINFO, "physinfo")
   S_(SECCLASS_XEN, XEN__QUIRK, "quirk")
   S_(SECCLASS_XEN, XEN__WRITECONSOLE, "writeconsole")
   S_(SECCLASS_XEN, XEN__READAPIC, "readapic")
   S_(SECCLASS_XEN, XEN__WRITEAPIC, "writeapic")
   S_(SECCLASS_XEN, XEN__PRIVPROFILE, "privprofile")
   S_(SECCLASS_XEN, XEN__NONPRIVPROFILE, "nonprivprofile")
   S_(SECCLASS_XEN, XEN__KEXEC, "kexec")
   S_(SECCLASS_DOMAIN, DOMAIN__SETVCPUCONTEXT, "setvcpucontext")
   S_(SECCLASS_DOMAIN, DOMAIN__PAUSE, "pause")
   S_(SECCLASS_DOMAIN, DOMAIN__UNPAUSE, "unpause")
   S_(SECCLASS_DOMAIN, DOMAIN__RESUME, "resume")
   S_(SECCLASS_DOMAIN, DOMAIN__CREATE, "create")
   S_(SECCLASS_DOMAIN, DOMAIN__MAX_VCPUS, "max_vcpus")
   S_(SECCLASS_DOMAIN, DOMAIN__DESTROY, "destroy")
   S_(SECCLASS_DOMAIN, DOMAIN__SETVCPUAFFINITY, "setvcpuaffinity")
   S_(SECCLASS_DOMAIN, DOMAIN__GETVCPUAFFINITY, "getvcpuaffinity")
   S_(SECCLASS_DOMAIN, DOMAIN__SCHEDULER, "scheduler")
   S_(SECCLASS_DOMAIN, DOMAIN__GETDOMAININFO, "getdomaininfo")
   S_(SECCLASS_DOMAIN, DOMAIN__GETVCPUINFO, "getvcpuinfo")
   S_(SECCLASS_DOMAIN, DOMAIN__GETVCPUCONTEXT, "getvcpucontext")
   S_(SECCLASS_DOMAIN, DOMAIN__SETDOMAINMAXMEM, "setdomainmaxmem")
   S_(SECCLASS_DOMAIN, DOMAIN__SETDOMAINHANDLE, "setdomainhandle")
   S_(SECCLASS_DOMAIN, DOMAIN__SETDEBUGGING, "setdebugging")
   S_(SECCLASS_DOMAIN, DOMAIN__HYPERCALL, "hypercall")
   S_(SECCLASS_DOMAIN, DOMAIN__TRANSITION, "transition")
   S_(SECCLASS_DOMAIN, DOMAIN__SETTIME, "settime")
   S_(SECCLASS_DOMAIN, DOMAIN__SHUTDOWN, "shutdown")
   S_(SECCLASS_DOMAIN, DOMAIN__SETADDRSIZE, "setaddrsize")
   S_(SECCLASS_DOMAIN, DOMAIN__GETADDRSIZE, "getaddrsize")
   S_(SECCLASS_HVM, HVM__SETHVMC, "sethvmc")
   S_(SECCLASS_HVM, HVM__GETHVMC, "gethvmc")
   S_(SECCLASS_HVM, HVM__SETPARAM, "setparam")
   S_(SECCLASS_HVM, HVM__GETPARAM, "getparam")
   S_(SECCLASS_HVM, HVM__PCILEVEL, "pcilevel")
   S_(SECCLASS_HVM, HVM__IRQLEVEL, "irqlevel")
   S_(SECCLASS_HVM, HVM__PCIROUTE, "pciroute")
   S_(SECCLASS_EVENT, EVENT__BIND, "bind")
   S_(SECCLASS_EVENT, EVENT__CLOSE, "close")
   S_(SECCLASS_EVENT, EVENT__SEND, "send")
   S_(SECCLASS_EVENT, EVENT__STATUS, "status")
   S_(SECCLASS_EVENT, EVENT__UNMASK, "unmask")
   S_(SECCLASS_EVENT, EVENT__NOTIFY, "notify")
   S_(SECCLASS_EVENT, EVENT__CREATE, "create")
   S_(SECCLASS_EVENT, EVENT__ALLOC, "alloc")
   S_(SECCLASS_EVENT, EVENT__VECTOR, "vector")
   S_(SECCLASS_EVENT, EVENT__RESET, "reset")
   S_(SECCLASS_GRANT, GRANT__MAP_READ, "map_read")
   S_(SECCLASS_GRANT, GRANT__MAP_WRITE, "map_write")
   S_(SECCLASS_GRANT, GRANT__UNMAP, "unmap")
   S_(SECCLASS_GRANT, GRANT__TRANSFER, "transfer")
   S_(SECCLASS_GRANT, GRANT__SETUP, "setup")
   S_(SECCLASS_GRANT, GRANT__COPY, "copy")
   S_(SECCLASS_GRANT, GRANT__QUERY, "query")
   S_(SECCLASS_MMU, MMU__MAP_READ, "map_read")
   S_(SECCLASS_MMU, MMU__MAP_WRITE, "map_write")
   S_(SECCLASS_MMU, MMU__PAGEINFO, "pageinfo")
   S_(SECCLASS_MMU, MMU__PAGELIST, "pagelist")
   S_(SECCLASS_MMU, MMU__ADJUST, "adjust")
   S_(SECCLASS_MMU, MMU__STAT, "stat")
   S_(SECCLASS_MMU, MMU__TRANSLATEGP, "translategp")
   S_(SECCLASS_MMU, MMU__UPDATEMP, "updatemp")
   S_(SECCLASS_MMU, MMU__PHYSMAP, "physmap")
   S_(SECCLASS_MMU, MMU__PINPAGE, "pinpage")
   S_(SECCLASS_MMU, MMU__MFNLIST, "mfnlist")
   S_(SECCLASS_MMU, MMU__MEMORYMAP, "memorymap")
   S_(SECCLASS_SHADOW, SHADOW__DISABLE, "disable")
   S_(SECCLASS_SHADOW, SHADOW__ENABLE, "enable")
   S_(SECCLASS_SHADOW, SHADOW__LOGDIRTY, "logdirty")
   S_(SECCLASS_RESOURCE, RESOURCE__ADD, "add")
   S_(SECCLASS_RESOURCE, RESOURCE__REMOVE, "remove")
   S_(SECCLASS_RESOURCE, RESOURCE__USE, "use")
   S_(SECCLASS_RESOURCE, RESOURCE__ADD_IRQ, "add_irq")
   S_(SECCLASS_RESOURCE, RESOURCE__REMOVE_IRQ, "remove_irq")
   S_(SECCLASS_RESOURCE, RESOURCE__ADD_IOPORT, "add_ioport")
   S_(SECCLASS_RESOURCE, RESOURCE__REMOVE_IOPORT, "remove_ioport")
   S_(SECCLASS_RESOURCE, RESOURCE__ADD_IOMEM, "add_iomem")
   S_(SECCLASS_RESOURCE, RESOURCE__REMOVE_IOMEM, "remove_iomem")
   S_(SECCLASS_SECURITY, SECURITY__COMPUTE_AV, "compute_av")
   S_(SECCLASS_SECURITY, SECURITY__COMPUTE_CREATE, "compute_create")
   S_(SECCLASS_SECURITY, SECURITY__COMPUTE_MEMBER, "compute_member")
   S_(SECCLASS_SECURITY, SECURITY__CHECK_CONTEXT, "check_context")
   S_(SECCLASS_SECURITY, SECURITY__LOAD_POLICY, "load_policy")
   S_(SECCLASS_SECURITY, SECURITY__COMPUTE_RELABEL, "compute_relabel")
   S_(SECCLASS_SECURITY, SECURITY__COMPUTE_USER, "compute_user")
   S_(SECCLASS_SECURITY, SECURITY__SETENFORCE, "setenforce")
   S_(SECCLASS_SECURITY, SECURITY__SETBOOL, "setbool")
   S_(SECCLASS_SECURITY, SECURITY__SETSECPARAM, "setsecparam")
