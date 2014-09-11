theory Examples
imports StanfordNetwork RoutingRange "../topoS/interface_abstraction/Network_ex" NetworkAnalysis
begin

interpretation example!: wellformed_network stanford_network
proof(unfold_locales)
  have all_sub1: "snd ` stanford_interface_links \<subseteq> set stanford_interfaces" by eval
  have all_sub2: "fst ` stanford_interface_links \<subseteq> set stanford_interfaces" by eval
  note all_sub = all_sub1 all_sub2
  case goal1 thus ?case unfolding stanford_network_def network_of_simps fst_add_backlinks Un_subset_iff using all_sub ..
  case goal2 thus ?case unfolding stanford_network_def network_of_simps snd_add_backlinks Un_subset_iff using all_sub ..
  case goal3 thus ?case by(simp add: stanford_network_def network_of_def)
  case goal4 thus ?case by(simp add: stanford_defs network_of_def)
qed (* isar proofs can be deferred, remember? *)
lemma wellformed_network_stanford_network: "wellformed_network stanford_network" by(unfold_locales)

lemma "valid_network_formers(set stanford_interfaces)
	(add_backlinks stanford_interface_links)
	stanford_forwarding_map"
unfolding valid_network_formers_def
proof(rule conjI[rotated])+
  case goal1 show ?case by eval
  case goal2 show ?case by eval
  case goal3 show ?case unfolding set_map[symmetric] foldr_True_set[symmetric] by eval
  case goal4 show ?case using wellformed_network_stanford_network[unfolded stanford_network_def] . next
qed

definition "some_packet = ( goza_rtr_repr, yoza_rtr_repr )"
definition "other_packet = ( cozb_rtr_repr, bbra_rtr_repr )"
thm other_packet_def

value "map_hdr dotteddecimal_of_ipv4addr some_packet"

value "packet_routing_table_semantics yoza_rtr_fwd_table (some_packet)"
value "packet_routing_table_semantics yoza_rtr_fwd_table (other_packet)"

value "packet_routing_table_semantics goza_rtr_fwd_table (some_packet)"

(*value "viewrange (prefix_to_range \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (192,168,0,0), pfxm_length = 24 \<rparr>)"*)
value "range_destination yoza_rtr_fwd_table (prefix_to_range
  \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (192,168,0,0), pfxm_length = 20 \<rparr>)"

value[code] "traverse_code stanford_network some_packet goza_rtr_te2_3"
value[code] "traverse_code stanford_network some_packet cozb_rtr_te3_1"
(* somehow, i'm not fazed *)
value[code] "succ_code stanford_network goza_rtr_te2_3"

value[code] "reachable_code stanford_network some_packet goza_rtr_te2_3"
(* "{\<lparr>entity = NetworkBox 0xAB40F905, port = Port 100012\<rparr>, \<lparr>entity = NetworkBox 0xAB406202, port = Port 1500006\<rparr>,
  \<lparr>entity = NetworkBox 0xAB406203, port = Port 1600005\<rparr>, \<lparr>entity = NetworkBox 0xAB42FC03, port = Port 800007\<rparr>}" *)

(*export_code stanford_network reachable_code covering_iplist some_packet in Haskell module_name SNE file exp*)

end
