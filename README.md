# Xen Copy-On-Write Checkpoints

## Overview
This modified version of Xen 3.2.2 provides the ability to take copy-on-write checkpoints 
of running VMs (PV and HVM). Its design and implementation is described in the 2010 report, 
"[Fast, Lightweight Virtual Machine Checkpointing](https://smartech.gatech.edu/bitstream/handle/1853/36671/git-cercs-10-05.pdf)".

## Assumptions
* 32-bit Xen hypervisor & 32-bit PV or 32-bit HVM guest
* PAE mode not supported
* `SHADOW OPTIMIZATIONS` turned off and `SHOPT_PREFETCH` turned off

## Implementation Details
* Shadow log-dirty mode is utilized to intercept memory writes. All pages are marked 
  as read-only. Writes are intercepted, target page is marked dirty, and page made 
  writable.

* CoW hypercall allows CoW checkpoint mode to be turned on/off. Turns shadow log-dirty 
  mode on/off and marks hypervisor in CoW mode.

* Properly handles competing writes from dom0 copy process and CoW handler. CoW copies 
  occur to separate 'diff' buffer which are then merged on top of actual copy buffer 
  used by dom0 copy process.

* The `xm save` command has been overridden to always perform CoW checkpoints, i.e. 
  the `-c` option has no use/meaning.

## Author
Mike Sun <<msun@gatech.edu>>

## Acknowledgements
Thanks to [Artem Dinaburg](http://dinaburg.org) for providing code to walk shadow page tables, 
Mike Hibler and the [Emulab](http://emulab.net) for their help in setting up a testbed, and 
Doug Blough for his guidance.
