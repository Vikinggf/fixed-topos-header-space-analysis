#!/usr/bin/python
#'''
#Created on Mar 2, 2014
#
#@author: Julius Michaelis
#'''
# copied from gen_stanford_thy.py
# generates a small graphiz file that vizualizes the connections between all routers, no interfaces
#
# Runs on the old version of hassel
# export PYTHONPATH=$PWD/hassel-public/hsa-python
from examples.load_stanford_backbone import *

(ports_nametoid,ports_idtoname) = load_stanford_backbone_port_to_id_map()

filename = "StanfordRouterLinks"

opg = open("%s.dot"%filename, 'w')

opg.write("digraph rtr_links { concentrate=true \n")

port_hosts = {}
for (rtr_name,pmap) in ports_nametoid.items():
	for (portname,portid) in pmap.items():
		if portid in port_hosts:
			print "Warning, duplicate port id {}, already present in {}, ignored {}".format(portid, port_hosts[portid], rtr_name)
		else:
			port_hosts[portid] = rtr_name

ttf = load_stanford_backbone_ttf();
for rule in ttf.rules:
	if rule['action'] == 'link':
		for in_port in rule['in_ports']:
			#kazemian magic
			# router durchnummerien, ergebnis mal 100 000
			# interfaces durchnummerieren, mult mit 1
			# interface varianten mit +10 000 +20 000
			# hier wird das wieder rausstrippen
			s_port = ((in_port / 100000) * 100000) + (in_port % 10000)
			if not s_port in port_hosts:
				print "Warning, unknown source(?) port %d"%in_port
				continue
			for out_port in rule['out_ports']:
				d_port = out_port / 100000 * 100000 + out_port % 10000
				if not d_port in port_hosts:
					print "Warning, unknown destination(?) port %d"%out_port
					continue
				opg.write("{} -> {}\n".format(port_hosts[s_port], port_hosts[d_port]))
	else:
		print "Warning, TTF rule is not link."

opg.write("}\n")
opg.close()
