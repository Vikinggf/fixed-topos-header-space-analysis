#!/usr/bin/python
''' only works on an old version of hassel
export PYTHONPATH=$PWD/hassel-public-old/src
'''

from config_parser.cisco_router_parser import *
from headerspace.tf import *
from time import time, clock

st = time()
output_path = "tf_stanford_backbone"
rtr_names = [("bbra_rtr",0),
			 ("bbrb_rtr",0),
			 ("boza_rtr",0),
			 ("bozb_rtr",0),
			 ("coza_rtr",580),
			 ("cozb_rtr",580),
			 ("goza_rtr",0),
			 ("gozb_rtr",0),
			 ("poza_rtr",0),
			 ("pozb_rtr",0),
			 ("roza_rtr",0),
			 ("rozb_rtr",0),
			 ("soza_rtr",580),
			 ("sozb_rtr",580),
			 ("yoza_rtr",0),
			 ("yozb_rtr",0),
			 ]

def subnetsize(subnet):
	for i in range(0,32):
		j = 2 ** 32 - 2 ** i
		if subnet & j:
			continue
		return i
	return 32
id = 1
cs_list = {}
for (rtr_name,vlan) in rtr_names:
	cs = ciscoRouter(id)
	cs.name = rtr_name;
	cs.set_replaced_vlan(vlan)
	tf = TF(cs.HS_FORMAT()["length"]*2)
	tf.set_prefix_id(rtr_name)
	cs.read_arp_table_file("Stanford_backbone/%s_arp_table.txt"%rtr_name)
	cs.read_mac_table_file("Stanford_backbone/%s_mac_table.txt"%rtr_name)
	cs.read_config_file("Stanford_backbone/%s_config.txt"%rtr_name)
	cs.read_spanning_tree_file("Stanford_backbone/%s_spanning_tree.txt"%rtr_name)
	cs.read_route_file("Stanford_backbone/%s_route.txt"%rtr_name)
	cs.generate_port_ids([])
	#if rtr_name == "coza_rtr" or rtr_name == "cozb_rtr" or rtr_name == "soza_rtr" or rtr_name == "sozb_rtr" or rtr_name == "yoza_rtr" or rtr_name == "yozb_rtr":
	for (vlan, port) in cs.vlan_ports.items():
		iface = []
		if vlan[4:] in cs.port_subnets:
			for f in cs.port_subnets[vlan[4:]]:
				if f[0] is not None:
					iface.append((int_to_dotted_ip(f[0]), f[1]))
			#print "asdf: {}, {}, {}".format(vlan, port, ip)
		if not iface:
			iface.append(("0.0.0.0",32))
		for (ip,mask) in iface:
			print "insert into vlanmember (vlan, router, ip, mask) values ('{}','{}','{}','{}')".format(vlan[4:], rtr_name, ip, mask)

	id += 1
	cs_list[rtr_name] = cs
