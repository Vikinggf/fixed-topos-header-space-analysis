theory NetworkAnalysis
imports DisjunctIPs StanfordHelpers "../topoS/interface_abstraction/Network_ex"
begin

definition "valid_network_formers ifaces iface_links forwarding_map \<equiv>
  wellformed_network (network_of ifaces iface_links forwarding_map) \<and>
  (\<forall>tbl \<in> snd ` set forwarding_map. correct_routing tbl) \<and>
  entity ` ifaces \<subseteq> fst ` set forwarding_map \<and>
  single_valued (set forwarding_map)
"

lemma valid_network_formers_code[code_unfold]: "valid_network_formers = (\<lambda> i l t.
  wellformed_network (network_of i l t) \<and>
  foldr (op \<and>) (map (correct_routing \<circ> snd) t) True \<and>
  entity ` i \<subseteq> set (map fst t) \<and>
  single_valued (set t))"
  unfolding fun_eq_iff
  unfolding valid_network_formers_def
  unfolding set_map
  unfolding foldr_map
  unfolding comp_def
  unfolding foldr_True_set
  by simp


lemma valid_formers_valid_prefixes: "valid_network_formers i il fm \<Longrightarrow> all_valid_prefixes (map snd fm)"
  unfolding
    all_valid_prefixes_def
    valid_network_formers_def
    correct_routing_def
proof -
  case goal1
  have "\<forall>tbl\<in>set fm. valid_prefixes (snd tbl)" using goal1 by simp
  then show ?case by(induction fm) simp_all
qed

lemma view_hdr_infold:
  "view network header = view \<lparr> interfaces = interfaces network, 
    forwarding = (\<lambda> entity port hdr. (forwarding network) entity port header), links = links network \<rparr> header"
unfolding view_def traverse_def succ_def by(simp only: network.simps)

lemma fst_e_imp_snd_e: "e \<in> set (map fst tbls) \<Longrightarrow> (the \<circ> map_of tbls) e \<in> set (map snd tbls)"
  by(induction tbls) auto

lemma network_of_src_inv: "view (network_of i l tbls) (srca, dst) = view (network_of i l tbls) (srcb, dst)"
  unfolding network_of_def block_reoutput_def
  unfolding packet_routing_table_semantics_def
  unfolding dst_addr_def extract_addr_def snd_def
  unfolding view_def traverse_def succ_def
  unfolding network.simps
  by simp

lemma network_of_Host_eq_NB[simp]: "view (network_of i l tbls) (src, NetworkBox dst) = view (network_of i l tbls) (src, Host dst)"
  unfolding network_of_def block_reoutput_def
  unfolding packet_routing_table_semantics_def
  unfolding dst_addr_def extract_addr_def snd_def
  unfolding view_def traverse_def succ_def
  unfolding network.simps
  by simp

definition "all_views ifs ifls tbls \<equiv> (map (\<lambda>cdst. view (network_of ifs ifls tbls) (Host 0, Host cdst)) (covering_iplist (map snd tbls)))"

theorem all_views_complete:
  assumes "valid_network_formers i l tbls"
  shows "view (network_of i l tbls) pkg 
    \<in> set (all_views i l tbls)"
proof -
  obtain src wdst where pkg_split: "pkg = (src, wdst)" by force
  obtain dst where dst_split: "Host dst = wdst \<or> NetworkBox dst = wdst" by(metis entity.exhaust)
  let ?csrc = "Host 0" (* Arbitrary source in all_views *)
  note conjunct31 = conjunct1[OF conjunct2[OF conjunct2]]
  case goal1
  note covering_iplists_ex_representative_set[OF valid_formers_valid_prefixes[OF assms], of dst] 
    then guess reprS .. note lS = this
  let ?repr = "the (ipv4rq_lowest_element reprS)"
  have "\<not>ipv4rq_empty reprS" using lS(2) unfolding ipv4rq_empty_set_eq ipv4rq_element_set_eq by blast
  from ipv4rq_lowest_in[OF this, unfolded ipv4rq_element_set_eq] have representant_replacement: 
    "\<And>entity. entity \<in> set (map fst tbls) \<Longrightarrow> routing_table_semantics ((the \<circ> map_of tbls) entity) dst
    = routing_table_semantics ((the \<circ> map_of tbls) entity) ?repr"
    using fst_e_imp_snd_e conjunct2[OF lS(2)] by fast
  have "view (network_of i l tbls) (src, Host dst) = view (network_of i l tbls) (src, Host ?repr)"
    using conjunct31[OF assms[unfolded valid_network_formers_def]] representant_replacement[simplified]
    by (subst view_hdr_infold)
       (subst view_hdr_infold[of _ "(src, Host ?repr)"], 
        unfold network_of_def block_reoutput_def packet_routing_table_semantics_def, simp only: network.simps,
        unfold view_def traverse_def succ_def dst_addr_f[where f = Host, simplified], simp, fast)
  moreover have "view (network_of i l tbls) (src, Host ?repr)
    \<in> set (map (\<lambda>cdst. view (network_of i l tbls) (?csrc, Host cdst)) (covering_iplist (map snd tbls)))"
    unfolding covering_iplist_def
    unfolding comp_def map_map set_map
    unfolding network_of_src_inv[where srca = ?csrc and srcb = src]
    using imageI[OF lS(1)]
    .
  from this[unfolded calculation[symmetric]]
  show ?case unfolding all_views_def unfolding pkg_split using dst_split network_of_Host_eq_NB by auto
qed

definition "all_views_code ifs ifls tbls \<equiv> (map (\<lambda>cdst. view_code (network_of ifs ifls tbls) (Host 0, Host cdst)) (covering_iplist (map snd tbls)))"

lemma all_views_code_correct:
  assumes "wellformed_network (network_of ifs ifls tbls)"
  shows "all_views ifs ifls tbls = all_views_code ifs ifls tbls"
  unfolding all_views_def all_views_code_def 
  unfolding view_code_correct[OF assms]
  ..

corollary all_network_analysis:
  assumes "valid_network_formers i l tbls"
  shows "(\<forall>x \<in> set (all_views i l tbls). analysis_fun x) \<Longrightarrow>
    \<not>(\<exists>y. \<not>analysis_fun (view (network_of i l tbls) y))"
using all_views_complete[OF assms] by simp

end
