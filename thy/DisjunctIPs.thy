theory DisjunctIPs
imports RoutingRange
begin

definition "alltablesets rtbl = fst ` reduced_ipset_destination rtbl UNIV"

fun allroutingsets :: "prefix_routing list \<Rightarrow> ipv4addr set set" where
  "allroutingsets [] = {UNIV}" |
  "allroutingsets [lasttbl] = alltablesets lasttbl" |
  "allroutingsets (tbl#rest) = 
    {a \<inter> b|a b. a \<in> allroutingsets rest \<and> b \<in> alltablesets tbl \<and> a \<inter> b \<noteq> {}}
  "

fun allroutingsets2 :: "prefix_routing list \<Rightarrow> ipv4addr set set" where
  "allroutingsets2 [] = {UNIV}" |
  "allroutingsets2 (tbl#rest) = 
    {a \<inter> b|a b. a \<in> allroutingsets2 rest \<and> b \<in> alltablesets tbl \<and> a \<inter> b \<noteq> {}}
  "

lemma "allroutingsets2 t = allroutingsets t"
  using ipset_left_side_nonempty
  apply(induction rule: allroutingsets.induct, simp_all add: alltablesets_def reduced_ipset_destination_def)

  oops


definition "all_valid_prefixes tbls \<equiv> foldr (op \<and>) (map valid_prefixes tbls) True"
lemma all_valid_prefixes_split: "all_valid_prefixes (t#ts) = (valid_prefixes t \<and> all_valid_prefixes ts)"
  unfolding all_valid_prefixes_def by simp
lemma alltablesets_parts: 
  assumes "valid_prefixes rtbl"
  shows "x \<in> alltablesets rtbl \<Longrightarrow> a \<in> x \<Longrightarrow> b \<in> x \<Longrightarrow> routing_table_semantics rtbl a = routing_table_semantics rtbl b"
  unfolding alltablesets_def
  by(clarify, metis iffD1[OF reduced_ipset_destination_correct[OF assms UNIV_I, symmetric]] fst_conv in_ipset_rel)

lemma allroutingsets_same_dst: "all_valid_prefixes rtbls \<Longrightarrow> 
  x \<in> allroutingsets rtbls \<Longrightarrow> 
  rtbl \<in> set rtbls \<Longrightarrow> 
  a \<in> x \<Longrightarrow> b \<in> x \<Longrightarrow> 
  routing_table_semantics rtbl a = routing_table_semantics rtbl b"
proof(induction arbitrary: x rule: allroutingsets.induct)
  case goal1 thus ?case by simp
next
  case goal2 thus ?case 
    using alltablesets_parts all_valid_prefixes_split goal2(1) alltablesets_def alltablesets_def
    by simp blast
next
  case goal3
  have ars_unfold: "allroutingsets (tbl # v # va) = {a \<inter> b |a b. a \<in> allroutingsets (v # va) \<and> b \<in> alltablesets tbl \<and> a \<inter> b \<noteq> {}}" unfolding allroutingsets.simps(3) ..
  note * = alltablesets_parts[OF _ _ goal3(5) goal3(6)]
  { fix c d :: "ipv4addr set"
    let ?int = "c \<inter> d"
    have "(c \<in> allroutingsets (v # va)) \<and> d \<in> alltablesets tbl \<and> c \<inter> d \<noteq> {} \<Longrightarrow> a \<in> ?int \<Longrightarrow> b \<in> ?int \<Longrightarrow> routing_table_semantics rtbl a = routing_table_semantics rtbl b"
      by (metis (full_types) Int_iff all_valid_prefixes_split alltablesets_parts goal3(1) goal3(2) goal3(4) set_ConsD)
      (* I don't even know why I proved this. I didn't even know it when I wrote it down. *)
  }
  then show ?case using goal3 by simp blast
qed

definition "alltablelists rtbl = map fst (reduced_range_destination rtbl ipv4rq_UNIV)"

lemma tablesetslists: "alltablesets rtbl = set (map ipv4rq_to_set (alltablelists rtbl))"
  unfolding alltablelists_def alltablesets_def
  unfolding ipv4rq_UNIV_set_eq[symmetric]
  unfolding reduced_range_destination_eq1[symmetric]
  unfolding set_map by force

fun allroutinglists :: "prefix_routing list \<Rightarrow> ipv4rq list" where
  "allroutinglists [] = [ipv4rq_UNIV]" | (* Debatable, but kills a few annoying assumptions *)
  "allroutinglists [lasttbl] = alltablelists lasttbl" |
  "allroutinglists (tbl#rest) = 
    concat (map (\<lambda>foo. filter (\<lambda>x. \<not> ipv4rq_empty x) (map (ipv4rq_intersection foo) (alltablelists tbl))) (allroutinglists rest))
  "

lemma routingsestslists: "allroutingsets rtbls = set (map ipv4rq_to_set (allroutinglists rtbls))"
  proof(induction rule: allroutinglists.induct)
    case goal1 thus ?case by simp
  next
    case goal2 show ?case using tablesetslists by simp
  next
    case goal3
    have mIH: "allroutingsets (v # va) = set (map ipv4rq_to_set (allroutinglists (v # va)))" using goal3(1) by simp
    have ***: "(map (map ipv4rq_to_set)
                  (map (\<lambda>foo. [x\<leftarrow>map (ipv4rq_intersection foo) (alltablelists tbl) . ipv4rq_to_set x \<noteq> {}])
                    (allroutinglists (v # va)))) = 
               map (map ipv4rq_to_set \<circ> (\<lambda>foo. [x\<leftarrow>map (ipv4rq_intersection foo) (alltablelists tbl) . ipv4rq_to_set x \<noteq> {}])) (allroutinglists (v # va))" by simp
    have **: "(map (map ipv4rq_to_set)
                  (map (\<lambda>foo. [x\<leftarrow>map (ipv4rq_intersection foo) (alltablelists tbl) . ipv4rq_to_set x \<noteq> {}])
                    (allroutinglists (v # va)))) = 
           map (\<lambda>foo. [x\<leftarrow>map (ipv4rq_to_set \<circ> ipv4rq_intersection foo) (alltablelists tbl) . x \<noteq> {}])
      (allroutinglists (v # va))"
      unfolding *** unfolding map_map filter_map unfolding comp_def by simp
    show ?case
      unfolding allroutingsets.simps allroutinglists.simps
      unfolding ipv4rq_empty_set_eq
      unfolding tablesetslists
      unfolding mIH
      unfolding map_concat
      unfolding **
      by fastforce
qed

lemma allroutingsets_UNIV: "\<Union>allroutingsets rtbls = UNIV"
proof(induction rule: allroutingsets.induct)
  case goal1 thus ?case by simp
next
  case goal2 thus ?case
    unfolding allroutingsets.simps(2) alltablesets_def
    unfolding reduced_ipset_destination_def
    unfolding left_reduce_preimage_stable
    using ipset_destination_complete by simp
next
  case goal3
  have mIH: "\<Union>allroutingsets (v # va) = UNIV" using goal3(1) by simp
  moreover
  have "\<Union>(fst ` reduced_ipset_destination tbl UNIV) = UNIV" 
    unfolding reduced_ipset_destination_def
    unfolding left_reduce_preimage_stable
    using ipset_destination_complete[unfolded complete_lattice_class.SUP_def] .
  note Union_intersection_helper[OF calculation this]
  then show ?case unfolding allroutingsets.simps alltablesets_def by simp
qed

lemma allroutinglists_same_dst:
  assumes "all_valid_prefixes rtbls" 
      and "r \<in> set (allroutinglists rtbls)" 
      and "ipv4rq_element x r"
      and "ipv4rq_element y r"
      and "tbl \<in> set rtbls"
    shows "routing_table_semantics tbl x = routing_table_semantics tbl y"
proof -
  note a = allroutingsets_same_dst[OF assms(1)]
  note b = routingsestslists
  from assms(2) have d: "ipv4rq_to_set r \<in> allroutingsets rtbls" unfolding b by simp
  have e: "x \<in> ipv4rq_to_set r" "y \<in> ipv4rq_to_set r" using assms(3) assms(4) unfolding ipv4rq_element_set_eq .
  show ?thesis using a[OF d assms(5) e] .
qed

lemma allroutinglists_UNIV:
  "\<Union>set (map ipv4rq_to_set (allroutinglists rtbls)) = UNIV"
  using allroutingsets_UNIV routingsestslists by simp

definition "covering_iplist \<equiv> map (the \<circ> ipv4rq_lowest_element) \<circ> allroutinglists"

lemma covering_iplists_ex_representative:
  assumes "all_valid_prefixes rtbls"
  shows "(\<exists>y \<in> set (covering_iplist rtbls). \<forall>rtbl \<in> set rtbls. routing_table_semantics rtbl x = routing_table_semantics rtbl y)"
unfolding covering_iplist_def comp_def
proof(clarsimp)
  case goal1
  have "\<exists>r \<in> set (allroutinglists rtbls). x \<in> ipv4rq_to_set r" 
    using allroutinglists_UNIV by fastforce
  then guess r .. note rl = this
  have ll: "the (ipv4rq_lowest_element r) \<in> ipv4rq_to_set r"
  proof -
    case goal1
    have "\<not> ipv4rq_empty r" using rl(2) by force
    from ipv4rq_lowest_in[OF this] show ?case unfolding ipv4rq_element_set_eq .
  qed
  note allroutinglists_same_dst[OF assms rl(1), unfolded ipv4rq_element_set_eq, OF rl(2) ll]
  then show "\<exists>y\<in>set (allroutinglists rtbls).
    \<forall>rtbl\<in>set rtbls. routing_table_semantics rtbl x = routing_table_semantics rtbl (the (ipv4rq_lowest_element y))"
    using rl(1) by blast
qed

lemma covering_iplists_ex_representative_set:
  assumes "all_valid_prefixes rtbls"
  shows "(\<exists>S \<in> set (allroutinglists rtbls). ipv4rq_element x S \<and> (\<forall>y \<in> ipv4rq_to_set S. \<forall>rtbl \<in> set rtbls. 
    routing_table_semantics rtbl x = routing_table_semantics rtbl y))"
unfolding comp_def
proof -
  case goal1
  have "\<exists>r \<in> set (allroutinglists rtbls). x \<in> ipv4rq_to_set r" 
    using allroutinglists_UNIV by fastforce
  then guess r .. note rl = this
  note allroutinglists_same_dst[OF assms rl(1), unfolded ipv4rq_element_set_eq, OF rl(2)]
  then show "?thesis"
    using rl unfolding ipv4rq_element_set_eq by blast
qed

end
