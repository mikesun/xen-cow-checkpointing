#
# Copyright (c) 2005 XenSource Ltd.
#
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
#


dir=$(dirname "$0")
. "$dir/xen-hotplug-common.sh"
. "$dir/xen-network-common.sh"

findCommand "$@"

if [ "$command" != "online" ]  &&
   [ "$command" != "offline" ] &&
   [ "$command" != "add" ]     &&
   [ "$command" != "remove" ]
then
  log err "Invalid command: $command"
  exit 1
fi

case "$command" in
    add | remove)
        exit 0
        ;;
esac


# Parameters may be read from the environment, the command line arguments, and
# the store, with overriding in that order.  The environment is given by the
# driver, the command line is given by the Xend global configuration, and
# store details are given by the per-domain or per-device configuration.

evalVariables "$@"

ip=${ip:-}
ip=$(xenstore_read_default "$XENBUS_PATH/ip" "$ip")

# Check presence of compulsory args.
XENBUS_PATH="${XENBUS_PATH:?}"
vif="${vif:?}"


vifname=$(xenstore_read_default "$XENBUS_PATH/vifname" "")
if [ "$vifname" ]
then
  if [ "$command" == "online" ] && ! ip link show "$vifname" >&/dev/null
  then
    do_or_die ip link set "$vif" name "$vifname"
  fi
  vif="$vifname"
fi


frob_iptable()
{
  if [ "$command" == "online" ]
  then
    local c="-A"
  else
    local c="-D"
  fi

  iptables "$c" FORWARD -m physdev --physdev-in "$vif" "$@" -j ACCEPT \
    2>/dev/null ||
    [ "$c" == "-D" ] ||
    log err \
     "iptables $c FORWARD -m physdev --physdev-in $vif $@ -j ACCEPT failed.
If you are using iptables, this may affect networking for guest domains."
}


##
# Add or remove the appropriate entries in the iptables.  With antispoofing
# turned on, we have to explicitly allow packets to the interface, regardless
# of the ip setting.  If ip is set, then we additionally restrict the packets
# to those coming from the specified networks, though we allow DHCP requests
# as well.
#
handle_iptable()
{
  # Check for a working iptables installation.  Checking for the iptables
  # binary is not sufficient, because the user may not have the appropriate
  # modules installed.  If iptables is not working, then there's no need to do
  # anything with it, so we can just return.
  if ! iptables -L -n >&/dev/null
  then
    return
  fi

  if [ "$ip" != "" ]
  then
      local addr
      for addr in $ip
      do
        frob_iptable -s "$addr"
      done

      # Always allow the domain to talk to a DHCP server.
      frob_iptable -p udp --sport 68 --dport 67
  else
      # No IP addresses have been specified, so allow anything.
      frob_iptable
  fi
}


##
# ip_of interface
#
# Print the IP address currently in use at the given interface, or nothing if
# the interface is not up.
#
ip_of()
{
  ip addr show "$1" | awk "/^.*inet.*$1\$/{print \$2}" | sed -n '1 s,/.*,,p'
}


##
# dom0_ip
#
# Print the IP address of the interface in dom0 through which we are routing.
# This is the IP address on the interface specified as "netdev" as a parameter
# to these scripts, or eth0 by default.  This function will call fatal if no
# such interface could be found.
#
dom0_ip()
{
  local nd=${netdev:-eth0}
  local result=$(ip_of "$nd")
  if [ -z "$result" ]
  then
      fatal
"$netdev is not up.  Bring it up or specify another interface with " \
"netdev=<if> as a parameter to $0."
  fi
  echo "$result"
}
