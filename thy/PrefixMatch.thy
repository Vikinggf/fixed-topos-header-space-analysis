theory PrefixMatch
imports IPv4Addr "autocorres-0.98/lib/WordLemmaBucket"
begin

subsection{*Definition*}

record prefix_match =
  pfxm_prefix :: ipv4addr
  pfxm_length :: nat
abbreviation "pfxm_mask x \<equiv> mask (32 - pfxm_length x)"

definition valid_prefix :: "prefix_match \<Rightarrow> bool" where
  "valid_prefix pf = ((pfxm_mask pf) AND pfxm_prefix pf = 0)"
lemma valid_prefix_E: "valid_prefix pf \<Longrightarrow> ((pfxm_mask pf) AND pfxm_prefix pf = 0)" 
  unfolding valid_prefix_def .
lemma valid_preifx_alt_def: "valid_prefix p = (pfxm_prefix p AND (2 ^ (32 - pfxm_length p) - 1) = 0)"
  unfolding valid_prefix_def
  unfolding mask_def
  using word_bw_comms(1)
   arg_cong[where f = "\<lambda>x. (pfxm_prefix p && x - 1 = 0)"]
   shiftl_1
  by metis

subsection{*Address Semantics*}

definition prefix_match_semantics :: "prefix_match \<Rightarrow> ipv4addr \<Rightarrow> bool" where
(*"prefix_match_semantics m a = (pfxm_prefix m \<le> a \<and> a \<le> pfxm_prefix m OR ((1 << (32 - pfxm_length m)) - 1))"*)
"prefix_match_semantics m a = (pfxm_prefix m = (NOT pfxm_mask m) AND a)"

lemma zero_prefix_match_all: "valid_prefix m \<Longrightarrow> pfxm_length m = 0 \<Longrightarrow> prefix_match_semantics m ip"
  apply(unfold prefix_match_semantics_def)
  apply(simp)
  apply(subgoal_tac "pfxm_prefix m = 0")
   apply(metis mask_32_max_word word_bool_alg.compl_one word_bool_alg.conj_zero_left)
  apply(simp add: mask_32_max_word valid_prefix_def)
done

subsection{*Set Semantics*}

definition prefix_to_ipset :: "prefix_match \<Rightarrow> ipv4addr set" where
  "prefix_to_ipset pfx = {pfxm_prefix pfx .. pfxm_prefix pfx OR pfxm_mask pfx}"

lemma pfx_not_empty: "valid_prefix pfx \<Longrightarrow> prefix_to_ipset pfx \<noteq> {}"
  unfolding valid_prefix_def prefix_to_ipset_def by(simp add: le_word_or2)

definition ipset_prefix_match where 
  "ipset_prefix_match pfx rg = (let pfxrg = prefix_to_ipset pfx in (rg \<inter> pfxrg, rg - pfxrg))"
lemma ipset_prefix_match_m[simp]:  "fst (ipset_prefix_match pfx rg) = rg \<inter> (prefix_to_ipset pfx)" by(simp only: Let_def ipset_prefix_match_def, simp)
lemma ipset_prefix_match_nm[simp]: "snd (ipset_prefix_match pfx rg) = rg - (prefix_to_ipset pfx)" by(simp only: Let_def ipset_prefix_match_def, simp)
lemma ipset_prefix_match_distinct: "rpm = ipset_prefix_match pfx rg \<Longrightarrow> 
  (fst rpm) \<inter> (snd rpm) = {}" by force
lemma ipset_prefix_match_complete: "rpm = ipset_prefix_match pfx rg \<Longrightarrow> 
  (fst rpm) \<union> (snd rpm) = rg" by force
lemma rpm_m_dup_simp: "rg \<inter> fst (ipset_prefix_match (routing_match r) rg) = fst (ipset_prefix_match (routing_match r) rg)"
  by simp

subsection{*Equivalence Proofs*}

lemma helper1: "NOT (0\<Colon>32 word) = x\<^sub>1\<^sub>9 OR NOT x\<^sub>1\<^sub>9" using word_bool_alg.double_compl by simp
lemma helper2: "(x\<^sub>0\<Colon>32 word) AND NOT 0 = x\<^sub>0" by simp
lemma helper3: "(x\<^sub>4\<^sub>8\<Colon>32 word) OR x\<^sub>4\<^sub>9 = x\<^sub>4\<^sub>8 OR x\<^sub>4\<^sub>9 AND NOT x\<^sub>4\<^sub>8" using helper1 helper2 by (metis word_oa_dist2)

lemma pfx_match_addr_ipset: "valid_prefix rr \<Longrightarrow> prefix_match_semantics rr addr \<Longrightarrow> (addr \<in> prefix_to_ipset rr)"
  by(simp add: prefix_match_semantics_def prefix_to_ipset_def valid_prefix_def)
    (metis helper3 le_word_or2 word_and_le2 word_bool_alg.conj_commute word_bool_alg.disj_commute)
(* inversion should hold\<dots> *)

lemma packet_ipset_prefix_eq1:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  assumes "\<not>prefix_match_semantics match addr" 
  shows "addr \<in> (snd (ipset_prefix_match match addrrg))"
using assms
proof -
  have "pfxm_prefix match \<le> addr \<Longrightarrow> \<not> addr \<le> pfxm_prefix match || pfxm_mask match"
  proof -
    case goal1
    have a1: "pfxm_mask match AND pfxm_prefix match = 0"
      using assms(2) unfolding valid_prefix_def .
    have a2: "pfxm_prefix match \<noteq> NOT pfxm_mask match AND addr"
      using assms(3) unfolding prefix_match_semantics_def .
    have f1: "pfxm_prefix match = pfxm_prefix match AND NOT pfxm_mask match"
      using a1 by (metis mask_eq_0_eq_x word_bw_comms(1))
    hence f2: "\<forall>x\<^sub>1\<^sub>1. (pfxm_prefix match OR x\<^sub>1\<^sub>1) AND NOT pfxm_mask match = pfxm_prefix match OR x\<^sub>1\<^sub>1 AND NOT pfxm_mask match"
      by (metis word_bool_alg.conj_disj_distrib2)
    moreover
    { assume "\<not> pfxm_prefix match \<le> addr AND NOT pfxm_mask match"
      hence "\<not> (pfxm_prefix match \<le> addr \<and> addr \<le> pfxm_prefix match OR pfxm_mask match)"
        using f1 by (metis neg_mask_mono_le) }
    moreover
    { assume "pfxm_prefix match \<le> addr AND NOT pfxm_mask match \<and> addr AND NOT pfxm_mask match \<noteq> (pfxm_prefix match OR pfxm_mask match) AND NOT pfxm_mask match"
      hence "\<exists>x\<^sub>0. \<not> addr AND NOT mask x\<^sub>0 \<le> (pfxm_prefix match OR pfxm_mask match) AND NOT mask x\<^sub>0"
        using f2 by (metis dual_order.antisym word_bool_alg.conj_cancel_right word_log_esimps(3))
      hence "\<not> (pfxm_prefix match \<le> addr \<and> addr \<le> pfxm_prefix match OR pfxm_mask match)"
        using neg_mask_mono_le by auto }
    ultimately show "?case"
      using a2 by (metis goal1 word_bool_alg.conj_cancel_right word_bool_alg.conj_commute word_log_esimps(3))
  qed
  from this show ?thesis using assms(1)
    unfolding ipset_prefix_match_def Let_def snd_conv prefix_to_ipset_def
    by simp
qed

lemma packet_ipset_prefix_eq2:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  assumes "prefix_match_semantics match addr" 
  shows "addr \<in> (fst (ipset_prefix_match match addrrg))"
using assms
  apply(subst ipset_prefix_match_def)
  apply(simp only: Let_def fst_def Case_def)
  apply(simp add: prefix_to_ipset_def)
  apply(transfer)
  apply(simp only: prefix_match_semantics_def valid_prefix_def)
  apply(simp add: word_and_le1)
  apply(metis helper3 le_word_or2 word_bw_comms(1) word_bw_comms(2))
done

lemma packet_ipset_prefix_eq3:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  assumes "addr \<in> (snd (ipset_prefix_match match addrrg))"
  shows "\<not>prefix_match_semantics match addr"
using assms
  apply(subst(asm) ipset_prefix_match_def)
  apply(simp only: Let_def fst_def Case_def)
  apply(simp)
  apply(subst(asm) prefix_to_ipset_def)
  apply(transfer)
  apply(simp only: prefix_match_semantics_def valid_prefix_def Set_Interval.ord_class.atLeastAtMost_iff prefix_to_ipset_def)
  apply(simp)
  apply(metis helper3 le_word_or2 word_and_le2 word_bw_comms(1) word_bw_comms(2))
done

lemma packet_ipset_prefix_eq4:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  assumes "addr \<in> (fst (ipset_prefix_match match addrrg))"
  shows "prefix_match_semantics match addr"
using assms
proof -
  have "pfxm_prefix match = ~~ pfxm_mask match && addr"
  proof -
    have a1: "pfxm_mask match && pfxm_prefix match = 0" using assms(2) unfolding valid_prefix_def .
    have a2: "pfxm_prefix match \<le> addr \<and> addr \<le> pfxm_prefix match || pfxm_mask match"
      using assms(3) unfolding ipset_prefix_match_def Let_def fst_conv prefix_to_ipset_def by simp
    have f2: "\<forall>x\<^sub>0. pfxm_prefix match && ~~ mask x\<^sub>0 \<le> addr && ~~ mask x\<^sub>0"
      using a2 neg_mask_mono_le by blast
    have f3: "\<forall>x\<^sub>0. addr && ~~ mask x\<^sub>0 \<le> (pfxm_prefix match || pfxm_mask match) && ~~ mask x\<^sub>0"
      using a2 neg_mask_mono_le by blast
    have f4: "pfxm_prefix match = pfxm_prefix match && ~~ pfxm_mask match"
      using a1 by (metis mask_eq_0_eq_x word_bw_comms(1))
    hence f5: "\<forall>x\<^sub>6. (pfxm_prefix match || x\<^sub>6) && ~~ pfxm_mask match = pfxm_prefix match || x\<^sub>6 && ~~ pfxm_mask match"
      using word_ao_dist by (metis)
    have f6: "\<forall>x\<^sub>2 x\<^sub>3. addr && ~~ mask x\<^sub>2 \<le> x\<^sub>3 \<or> \<not> (pfxm_prefix match || pfxm_mask match) && ~~ mask x\<^sub>2 \<le> x\<^sub>3"
      using f3 dual_order.trans by auto
    have "pfxm_prefix match = (pfxm_prefix match || pfxm_mask match) && ~~ pfxm_mask match"
      using f5 by auto
    hence "pfxm_prefix match = addr && ~~ pfxm_mask match"
      using f2 f4 f6 by (metis eq_iff)
    thus "pfxm_prefix match = ~~ pfxm_mask match && addr"
      by (metis word_bw_comms(1))
  qed
  from this show ?thesis unfolding prefix_match_semantics_def .
qed

lemma packet_ipset_prefix_eq24:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  shows "prefix_match_semantics match addr = (addr \<in> (fst (ipset_prefix_match match addrrg)))"
using packet_ipset_prefix_eq2[OF assms] packet_ipset_prefix_eq4[OF assms] by fast

lemma packet_ipset_prefix_eq13:
  assumes "addr \<in> addrrg"
  assumes "valid_prefix match"
  shows "\<not>prefix_match_semantics match addr = (addr \<in> (snd (ipset_prefix_match match addrrg)))"
using packet_ipset_prefix_eq1[OF assms] packet_ipset_prefix_eq3[OF assms] by fast

lemma prefix_match_if_in_my_set: "valid_prefix pfx \<Longrightarrow> 
  prefix_match_semantics pfx (a :: ipv4addr) \<longleftrightarrow> a \<in> prefix_to_ipset pfx"
  using packet_ipset_prefix_eq24 by auto

lemma prefix_match_if_in_corny_set: 
  assumes "valid_prefix pfx"
  shows "prefix_match_semantics pfx (a :: ipv4addr) \<longleftrightarrow> a \<in> ipv4range_set_from_netmask (pfxm_prefix pfx) (NOT pfxm_mask pfx)"
  unfolding prefix_match_if_in_my_set[OF assms]
  unfolding prefix_to_ipset_def ipv4range_set_from_netmask_def Let_def
  unfolding word_bool_alg.double_compl
  proof -
    case goal1
    have *: "pfxm_prefix pfx && ~~ pfxm_mask pfx = pfxm_prefix pfx"
      unfolding mask_eq_0_eq_x[symmetric] using valid_prefix_E[OF assms] word_bw_comms(1)[of "pfxm_prefix pfx"] by simp
    hence **: "pfxm_prefix pfx && ~~ pfxm_mask pfx || pfxm_mask pfx = pfxm_prefix pfx || pfxm_mask pfx"
      by simp
    show ?case unfolding * ** ..
  qed

subsection{*Range stuff*}

definition prefix_to_range :: "prefix_match \<Rightarrow> ipv4rq" where
  "prefix_to_range pfx = [pfxm_prefix pfx; pfxm_prefix pfx OR pfxm_mask pfx]"
lemma prefix_to_range_set_eq: "ipv4rq_to_set (prefix_to_range pfx) = prefix_to_ipset pfx"
  unfolding prefix_to_range_def prefix_to_ipset_def by transfer simp

definition "range_prefix_match pfx rg \<equiv> (let pfxrg = prefix_to_range pfx in 
  (ipv4rq_intersection rg pfxrg, ipv4rq_setminus rg pfxrg))"
lemma range_prefix_match_set_eq:
  "(\<lambda>(r1,r2). (ipv4rq_to_set r1, ipv4rq_to_set r2)) (range_prefix_match pfx rg) = ipset_prefix_match pfx (ipv4rq_to_set rg)"
  unfolding range_prefix_match_def ipset_prefix_match_def Let_def 
  using ipv4rq_intersection_set_eq ipv4rq_setminus_set_eq prefix_to_range_set_eq  by simp
lemma range_prefix_match_sm[simp]:  "ipv4rq_to_set (fst (range_prefix_match pfx rg)) = fst (ipset_prefix_match pfx (ipv4rq_to_set rg))"
  by (metis fst_conv ipset_prefix_match_m  ipv4rq_intersection_set_eq prefix_to_range_set_eq range_prefix_match_def)
lemma range_prefix_match_snm[simp]: "ipv4rq_to_set (snd (range_prefix_match pfx rg)) = snd (ipset_prefix_match pfx (ipv4rq_to_set rg))"
  by (metis snd_conv ipset_prefix_match_nm ipv4rq_setminus_set_eq     prefix_to_range_set_eq range_prefix_match_def)

end