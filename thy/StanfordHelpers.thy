theory StanfordHelpers
imports Routing
begin

definition "map_entity f e = (case e of NetworkBox a \<Rightarrow> NetworkBox (f a) | Host a \<Rightarrow> Host (f a))"
definition "map_hdr f hdr = (case hdr of (src,dst) \<Rightarrow> (map_entity f src, map_entity f dst))"

definition add_backlinks :: "(('v interface) \<times> ('v interface)) set \<Rightarrow> (('v interface) \<times> ('v interface)) set" where
  "add_backlinks lks = lks \<union> { (to, from) |from to. (from, to) \<in> lks }"
lemma snd_add_backlinks: "snd ` add_backlinks x = snd ` x \<union> fst ` x"
  unfolding add_backlinks_def image_Un by force
lemma fst_add_backlinks: "fst ` add_backlinks x = snd ` x \<union> fst ` x"
  unfolding add_backlinks_def image_Un by force
lemma finite_mod: "finite x \<Longrightarrow> finite {f e|e. e \<in> x}" by simp
lemma finite_add_backlinks_finite[simp]: "finite (add_backlinks l) = finite l"
  unfolding add_backlinks_def 
  proof
    let ?backlinks = "{(to, from) |from to. (from, to) \<in> l}"
    have *: "?backlinks = {(snd e, fst e)|e. e \<in> l}" by simp
    case goal2
    have "finite ?backlinks" using finite_mod[OF goal2] * by metis
    with goal2 show "finite (l \<union> ?backlinks)" by simp
qed simp

definition "block_reoutput fwd_fun = (\<lambda>e p h. fwd_fun e p h - {p})"

definition "network_of ifaces iface_links forwarding_map \<equiv> \<lparr>
	interfaces = ifaces,
	forwarding = (block_reoutput
    (\<lambda> entity port header. packet_routing_table_semantics ((the \<circ> map_of forwarding_map) entity) header)),
	links = iface_links
\<rparr>"

lemma network_of_simps: "interfaces (network_of i l tbl) = i" "links (network_of i l tbl) = l"
  unfolding network_of_def
  unfolding network.simps
  by(rule refl, rule refl)

end
