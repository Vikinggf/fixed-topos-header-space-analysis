theory SimpleNetwork
imports NetworkAnalysis
begin

definition "router   = ipv4addr_of_dotteddecimal (1,0,1,1)"
definition "normal   = ipv4addr_of_dotteddecimal (1,0,1,2)"
definition "weird    = ipv4addr_of_dotteddecimal (1,0,2,3)"
definition "daisy    = ipv4addr_of_dotteddecimal (1,0,3,4)"
definition "wlan1    = ipv4addr_of_dotteddecimal (1,0,4,5)"
definition "wlan2    = ipv4addr_of_dotteddecimal (1,0,4,6)"
definition "internet = ipv4addr_of_dotteddecimal (2,0,0,7)"
lemmas entity_defs = router_def normal_def daisy_def weird_def wlan1_def wlan2_def internet_def

definition "simple_links = add_backlinks {
  (\<lparr> entity = NetworkBox router, port = Port 11 \<rparr>, \<lparr> entity = Host normal, port = Port 12 \<rparr>),
  (\<lparr> entity = NetworkBox router, port = Port 21 \<rparr>, \<lparr> entity = NetworkBox weird, port = Port 23 \<rparr>),
  (\<lparr> entity = NetworkBox weird, port = Port 33 \<rparr>,  \<lparr> entity = Host daisy, port = Port 34 \<rparr>),
  (\<lparr> entity = NetworkBox router, port = Port 41 \<rparr>, \<lparr> entity = Host wlan1, port = Port 45 \<rparr>),
  (\<lparr> entity = NetworkBox router, port = Port 41 \<rparr>, \<lparr> entity = Host wlan2, port = Port 46 \<rparr>),
  (\<lparr> entity = Host wlan1, port = Port 45 \<rparr>,        \<lparr> entity = Host wlan2, port = Port 46 \<rparr>),
  (\<lparr> entity = NetworkBox router, port = Port 1 \<rparr>,  \<lparr> entity = Host internet, port = Port 7 \<rparr>)
}"

definition "router_fwd_table = [
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (1,0,1,1),pfxm_length = 32 \<rparr>, routing_action = {} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (1,0,2,1),pfxm_length = 32 \<rparr>, routing_action = {} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (1,0,4,1),pfxm_length = 32 \<rparr>, routing_action = {} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (2,0,0,1),pfxm_length = 32 \<rparr>, routing_action = {} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (1,0,1,0), pfxm_length = 24 \<rparr>, routing_action = Port ` {11} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (1,0,4,0), pfxm_length = 24 \<rparr>, routing_action = Port ` {41} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (1,0,2,0), pfxm_length = 23 \<rparr>, routing_action = Port ` {21} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = 0, pfxm_length = 0 \<rparr>, routing_action = Port ` {1} \<rparr>
]"
lemma "correct_routing router_fwd_table" by eval

definition "weirdbox_fwd_table = [
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (1,0,2,3),pfxm_length = 32 \<rparr>, routing_action = {} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (1,0,3,3),pfxm_length = 32 \<rparr>, routing_action = {} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = ipv4addr_of_dotteddecimal (1,0,3,0),pfxm_length = 24 \<rparr>, routing_action = Port ` {33} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = 0,pfxm_length = 0 \<rparr>, routing_action = Port ` {23} \<rparr>
]"
lemma "correct_routing weirdbox_fwd_table" by eval

definition "default_only own_addr default_port = [
	\<lparr> routing_match = \<lparr> pfxm_prefix = own_addr,pfxm_length = 32 \<rparr>, routing_action = {} \<rparr>,
	\<lparr> routing_match = \<lparr> pfxm_prefix = 0,pfxm_length = 0 \<rparr>, routing_action = Port ` {default_port} \<rparr>
]"
lemma "correct_routing (default_only addr defport)"
  unfolding default_only_def correct_routing_def valid_prefix_def valid_prefixes_def by simp

definition "forwarding_table_map = [
  (NetworkBox router, router_fwd_table),
  (NetworkBox weird, weirdbox_fwd_table),
  (Host daisy, default_only daisy 34),
  (Host wlan1, default_only wlan1 45),
  (Host wlan2, default_only wlan2 46),
  (Host normal, default_only normal 12),
  (Host internet, default_only normal 7)
]"

definition "to_fun m = (the \<circ> map_of m)"

definition "simple_interfaces \<equiv> fst ` simple_links \<union> snd ` simple_links"

lemma simple_valid_formed: "valid_network_formers simple_interfaces simple_links forwarding_table_map"
proof -
  have "(\<forall>tbl\<in>snd ` set forwarding_table_map. correct_routing tbl)" by eval
  moreover
  have "wellformed_network (network_of simple_interfaces simple_links forwarding_table_map)"
  proof(unfold_locales)
    case goal1 thus ?case by eval
  next
    case goal2 thus ?case by eval
  next
    case goal3 thus ?case by(simp add: simple_links_def simple_interfaces_def network_of_def)
  next
    case goal4 thus ?case
      unfolding network_of_def simple_links_def entity_defs simple_interfaces_def fst_add_backlinks snd_add_backlinks
      by(auto, (fastforce dest: ipv4addr_of_dotteddecimal_eqE)+)
  qed
  moreover
  have "entity ` simple_interfaces \<subseteq> fst ` set forwarding_table_map" by eval
  moreover
  have "single_valued (set forwarding_table_map)" 
    unfolding forwarding_table_map_def single_valued_def entity_defs 
    by(auto, (fastforce dest: ipv4addr_of_dotteddecimal_eqE)+)
  ultimately
  show ?thesis unfolding valid_network_formers_def by simp
qed

definition "simple_network \<equiv> network_of simple_interfaces simple_links forwarding_table_map"

interpretation simple_wellformed: wellformed_network simple_network
  unfolding simple_network_def using conjunct1[OF simple_valid_formed[unfolded valid_network_formers_def]] .

value "reduced_range_destination ((to_fun forwarding_table_map) (NetworkBox router)) ipv4rq_UNIV"
value "range_destination ((to_fun forwarding_table_map) (NetworkBox weird)) ipv4rq_UNIV"
value[code] "reachable_code simple_network (Host wlan1, Host wlan2)  \<lparr> entity = Host wlan1, port = Port 45 \<rparr>"
value[code] "reachable_code simple_network (Host normal, Host daisy)  \<lparr> entity = Host normal, port = Port 12 \<rparr>"
value[code] "reachable_code simple_network (Host internet, Host (daisy + 1))  \<lparr> entity = Host normal, port = Port 12 \<rparr>"
value[code] "reachable_code simple_network (Host daisy, Host internet)  \<lparr> entity = Host daisy, port = Port 34 \<rparr>"

lemma [code_unfold]:
  "all_views simple_interfaces simple_links forwarding_table_map = 
   all_views_code simple_interfaces simple_links forwarding_table_map"
  using all_views_code_correct[OF conjunct1[OF simple_valid_formed[unfolded valid_network_formers_def]]] .

value "covering_iplist (map snd forwarding_table_map)"
value "(map (\<lambda>cdst. (cdst, view_code (network_of simple_interfaces simple_links forwarding_table_map) (Host 0, Host cdst)))
   (covering_iplist (map snd forwarding_table_map)))"
value "(\<lambda>l. (length (remdups l), length l)) ((map (\<lambda>cdst. view_code (network_of simple_interfaces simple_links forwarding_table_map) (Host 0, Host cdst))
   (covering_iplist (map snd forwarding_table_map))))"

(* 
What you get if you don't block the reoutput:
""[{(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = Host 0x1000304, port = Port 34\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = Host 0x1000304, port = Port 34\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = Host 0x1000304, port = Port 34\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = Host 0x1000304, port = Port 34\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x2000007, port = Port 7\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x2000007, port = Port 7\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x2000007, port = Port 7\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x2000007, port = Port 7\<rparr>),
   (\<lparr>entity = Host 0x1000102, port = Port 12\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = Host 0x1000304, port = Port 34\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = Host 0x1000405, port = Port 45\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = Host 0x1000406, port = Port 46\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>),
   (\<lparr>entity = Host 0x2000007, port = Port 7\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>)}]"
  :: "(32 word interface \<times> 32 word interface) set list"

Otherwise:
"[{(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>, \<lparr>entity = Host 0x1000304, port = Port 34\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000102, port = Port 12\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000406, port = Port 46\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x1000405, port = Port 45\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 1\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = NetworkBox 0x1000203, port = Port 23\<rparr>)},
  {(\<lparr>entity = NetworkBox 0x1000101, port = Port 41\<rparr>, \<lparr>entity = Host 0x2000007, port = Port 7\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000203, port = Port 33\<rparr>, \<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 21\<rparr>, \<lparr>entity = Host 0x2000007, port = Port 7\<rparr>),
   (\<lparr>entity = NetworkBox 0x1000101, port = Port 11\<rparr>, \<lparr>entity = Host 0x2000007, port = Port 7\<rparr>)}]"
*)

end
