#!/usr/bin/python

import sys
import fileinput
import re
from config_parser.cisco_router_parser import *

def explain(array):
	array = ''.join(array.split(','))
	fmt = cisco_router.HS_FORMAT()
	for hdr in ["vlan", "ip_dst", "ip_src", "ip_proto", "transport_ctrl", "transport_dst", "transport_src"]:
		pos = fmt["%s_pos"%hdr]*8;
		length = fmt["%s_len"%hdr]*8;
		ss = array[pos:pos+length]
		infostr = ""
		if hdr in ["ip_src", "ip_dst"]:
			octets = []
			for i in [3,2,1,0]:
				octet = ss[i*8:i*8+8][::-1]
				try:
					octets.append(str(int(octet, 2)))
				except ValueError:
					octets.append('x')
			infostr = '.'.join(octets)
		print "{}: {} {}".format(hdr, ss, infostr)


if len(sys.argv) != 2:
	for array in sys.stdin:
		explain(array)
else:
	explain(sys.argv[1])

# pprints a HSA string
# Example:
#./explain_hsa_mask.py xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx0000001110000110
# vlan: 0110000111000000 
# ip_dst: xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx x.x.x.x
# ip_src: xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx x.x.x.x
# ip_proto: xxxxxxxx 
# transport_ctrl: xxxxxxxx 
# transport_dst: xxxxxxxxxxxxxxxx 
# transport_src: xxxxxxxxxxxxxxxx
#
# Best used as: while read hsam; do ./explain_hsa_mask.py $hsam; done
#
# Also accepts the newer, comma-format.
