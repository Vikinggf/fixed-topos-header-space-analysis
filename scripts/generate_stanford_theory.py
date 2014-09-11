#!/usr/bin/python
# @author: Julius Michaelis
# 
# Uses the cisco config parser
# Generates ../StanfordNetwork.thy, currenlty generates acl lists and routing functions

from config_parser.cisco_router_parser import *
from headerspace.tf import *
from time import time, clock

st = time()
output_path = "tf_stanford_backbone"
rtr_names = [("bbra_rtr",None),
			 ("bbrb_rtr",None),
			 ("boza_rtr",None),
			 ("bozb_rtr",None),
			 ("coza_rtr",(83,580)),
			 ("cozb_rtr",(83,580)),
			 ("goza_rtr",None),
			 ("gozb_rtr",None),
			 ("poza_rtr",None),
			 ("pozb_rtr",None),
			 ("roza_rtr",None),
			 ("rozb_rtr",None),
			 ("soza_rtr",(83,580)),
			 ("sozb_rtr",(83,580)),
			 ("yoza_rtr",None),
			 ("yozb_rtr",None),# 
			 ]

topology = [("bbra_rtr","te7/3","goza_rtr","te2/1"),
            ("bbra_rtr","te7/3","pozb_rtr","te3/1"),
            ("bbra_rtr","te1/3","bozb_rtr","te3/1"),
            ("bbra_rtr","te1/3","yozb_rtr","te2/1"),
            ("bbra_rtr","te1/3","roza_rtr","te2/1"),
            ("bbra_rtr","te1/4","boza_rtr","te2/1"),
            ("bbra_rtr","te1/4","rozb_rtr","te3/1"),
            ("bbra_rtr","te6/1","gozb_rtr","te3/1"),
            ("bbra_rtr","te6/1","cozb_rtr","te3/1"),
            ("bbra_rtr","te6/1","poza_rtr","te2/1"),
            ("bbra_rtr","te6/1","soza_rtr","te2/1"),
            ("bbra_rtr","te7/2","coza_rtr","te2/1"),
            ("bbra_rtr","te7/2","sozb_rtr","te3/1"),
            ("bbra_rtr","te6/3","yoza_rtr","te1/3"),
            ("bbra_rtr","te7/1","bbrb_rtr","te7/1"),
            ("bbrb_rtr","te7/4","yoza_rtr","te7/1"),
            ("bbrb_rtr","te1/1","goza_rtr","te3/1"),
            ("bbrb_rtr","te1/1","pozb_rtr","te2/1"),
            ("bbrb_rtr","te6/3","bozb_rtr","te2/1"),
            ("bbrb_rtr","te6/3","roza_rtr","te3/1"),
            ("bbrb_rtr","te6/3","yozb_rtr","te1/1"),
            ("bbrb_rtr","te1/3","boza_rtr","te3/1"),
            ("bbrb_rtr","te1/3","rozb_rtr","te2/1"),
            ("bbrb_rtr","te7/2","gozb_rtr","te2/1"),
            ("bbrb_rtr","te7/2","cozb_rtr","te2/1"),
            ("bbrb_rtr","te7/2","poza_rtr","te3/1"),
            ("bbrb_rtr","te7/2","soza_rtr","te3/1"),
            ("bbrb_rtr","te6/1","coza_rtr","te3/1"),
            ("bbrb_rtr","te6/1","sozb_rtr","te2/1"),
            ("boza_rtr","te2/3","bozb_rtr","te2/3"),
            ("coza_rtr","te2/3","cozb_rtr","te2/3"),
            ("goza_rtr","te2/3","gozb_rtr","te2/3"),
            ("poza_rtr","te2/3","pozb_rtr","te2/3"),
            ("roza_rtr","te2/3","rozb_rtr","te2/3"),
            ("soza_rtr","te2/3","sozb_rtr","te2/3"),
            ("yoza_rtr","te1/1","yozb_rtr","te1/3"),
            ("yoza_rtr","te1/2","yozb_rtr","te1/2"),
            ]

def chunks(l, n):
	if n < 1:
		n = 1
	return [l[i:i + n] for i in range(0, len(l), n)]

def subnetsize(subnet):
	for i in range(0,32):
		j = 2 ** 32 - 2 ** i
		if subnet & j:
			continue
		return i
	return 32
router_id = 1

def phyports(cs, fwd_port):
	phyport = [fwd_port]
	if fwd_rule[2].startswith('vlan'):
		if fwd_rule[2] in cs.vlan_span_ports.keys():
			port_list = cs.vlan_span_ports[fwd_rule[2]]
			for p in port_list:
				if p in cs.port_to_id.keys():
					phyport.append(p)
	return phyport

def ip_beauty(ip):
	return "ipv4addr_of_dotteddecimal ({})".format(re.sub(r'\.',r',', int_to_dotted_ip(ip)))
	#return "0x{:08x}".format(ip)

def get_protocol_name(proto_id):
	dict = {"51":"ah", "88":"eigrp", "50":"esp", "47":"gre", "1":"icmp", "2":"igmp", \
			"9":"igrp", "0":"ip", "94":"ipinip", "4":"nos", "89":"ospf", "6":"tcp", \
			"17":"udp"}
	if proto_id in dict.keys():
		return dict[proto_name]
	return None

cs_list = {}

opf = open("../thy/StanfordNetwork.thy", 'w')

definitions = ['map_entity', 'map_hdr', 'add_backlinks']
def define(name, text):
	opf.write("definition \"{} \<equiv> {}\"\n".format(name, text))
	definitions.append(name)
	return name

opf.write("(* Automatically generated file by scripts/gen_stanford2.py. Do not modify. Modify script and commit both. *)\n")
opf.write("theory StanfordNetwork\n")
opf.write("imports StanfordHelpers\n")
opf.write("begin\n")
ptcs = []
tbl_names = []
nw_fwd_table_entries = []
router_ips = {}
for (rtr_name,vlan) in rtr_names:
	opf.write("\n(* router %s *)\n"%rtr_name)
	cs = cisco_router(router_id)
	cs.name = rtr_name;
	cs.set_replaced_vlan(vlan)
	tf = TF(cs.HS_FORMAT()["length"]*2)
	tf.set_prefix_id(rtr_name)
	#if rtr_name != "yoza_rtr":
	#	continue
	cs.read_arp_table_file("Stanford_backbone/%s_arp_table.txt"%rtr_name)
	cs.read_mac_table_file("Stanford_backbone/%s_mac_table.txt"%rtr_name)
	cs.read_config_file("Stanford_backbone/%s_config.txt"%rtr_name)
	cs.read_spanning_tree_file("Stanford_backbone/%s_spanning_tree.txt"%rtr_name)
	cs.read_route_file("Stanford_backbone/%s_route.txt"%rtr_name)
	cs.generate_port_ids([])
	cs.optimize_forwarding_table()

	# There's a problem in the analysis: The packets are directed at boxes, but the boxes have multiple addresses
	# Hack fix: Just chose one. It doesn't matter which, anyway
	rtr_ip = "NetworkBox ({})".format(ip_beauty(cs.port_ips.itervalues().next()))
	router_ips[rtr_name] = "{}_repr".format(rtr_name)
	opf.write("abbreviation \"{} \<equiv> NetworkBox 0x{:08x}\"\n".format(router_ips[rtr_name], cs.port_ips.itervalues().next()))

	fwd_tbl_name = "%s_fwd_table"%rtr_name
	tbl_names.append(fwd_tbl_name)
	rrules = []
	for subnet in range(32,-1,-1):
		for fwd_rule in cs.fwd_table:
			if fwd_rule[1] != subnet:
				continue
			ip = fwd_rule[0]
			out_ports = fwd_rule[2]
			match = "\<lparr> pfxm_prefix = {}, pfxm_length = {} \<rparr>".format(\
				ip_beauty(ip), subnet)
			action = "{}"
			f_out_ports = [str(cs.port_to_id[op.split('.')[0]]) for op in phyports(cs, out_ports) if op != "self" and not op.startswith("vlan")]
			if len(f_out_ports) > 0:
				action = "Port ` {" + ",".join(f_out_ports) + "}"
			rrules.append("\t\<lparr> routing_match = {}, routing_action = {} \<rparr>".format(match, action))
	# split up large tables so Isabelle doesn't hang for so long...
	rule_chunks = chunks(rrules, 150)
	previous_chunk = ""
	for i,c in reversed(list(enumerate(rule_chunks))):
		if i == 0:
			fwd_tbl_cname = fwd_tbl_name
		else:
			fwd_tbl_cname = "{}_cont{}".format(fwd_tbl_name, i)
		define(fwd_tbl_cname, "[\n{}\n]{}".format(",\n".join(c), "" if previous_chunk == "" else " @ %s\n"%previous_chunk))
		previous_chunk = fwd_tbl_cname

	opf.write("lemma {}_fwd_table_correct: \"correct_routing {}\" by eval\n\n".format(rtr_name, fwd_tbl_name))

	nw_fwd_table_entries.append("({}, {})".format(rtr_ip, fwd_tbl_name))

	# acl generation was here. fetch from repo if needed.
	
	router_id += 1
	cs_list[rtr_name] = cs
opf.write("\n")

define("stanford_routing_tables", "\n\t[{}]".format(", ".join(tbl_names)))
define("stanford_forwarding_map", "[\n\t{}\n]".format(",\n\t".join(nw_fwd_table_entries)))
opf.write("\n")

def clean_ifnam(port):
	return port.replace("/","_").replace("-","_")
def entitynam(router, port):
	return "{}_{}".format(router, clean_ifnam(port))

ifaces = []
for rtr in cs_list.keys():
	cs = cs_list[rtr]
	for p in cs.port_to_id.keys():
		defname = entitynam(rtr,p)
		define(defname, "\<lparr> entity = {}, port = Port {}\<rparr>".format(router_ips[rtr], cs.port_to_id[p]))
		ifaces.append(defname)
opf.write("\n")
define("stanford_interfaces", "[\n\t{}\n] :: ipv4addr interface list".format(",\n\t".join(ifaces)))
opf.write("\n")

ifaceconns = []
for (from_router,from_port,to_router,to_port) in topology:
	ifaceconns.append("\t({}, {})".format(entitynam(from_router, from_port), entitynam(to_router, to_port)))
define("stanford_interface_links", "{}\n{}\n{}".format("{", ",\n".join(ifaceconns), "} :: (ipv4addr interface \<times> ipv4addr interface) set"))

define("stanford_network", """network_of
	(set stanford_interfaces)
	(add_backlinks stanford_interface_links)
	stanford_forwarding_map""")

opf.write("\nlemmas stanford_defs = {}\n\n".format("\n\t".join(["_def ".join(line) + "_def" for line in chunks(definitions,5)])))

opf.write("\nend\n")
opf.close()
