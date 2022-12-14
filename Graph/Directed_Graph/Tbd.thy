(* TODO Move. *)
(* TODO Rename. *)
theory Tbd
  imports
    Directed_Walk
begin

locale tbd =
  fixes m :: "'b \<rightharpoonup> 'a \<times> 'b"
  assumes wf: "wf {(u, v). \<exists>\<epsilon>. m v = Some (\<epsilon>, u)}"
begin

function (domintros) follow :: "'b \<Rightarrow> ('a, 'b) edge list" where
  "follow v = (case m v of None \<Rightarrow> [] | Some (\<epsilon>, u) \<Rightarrow> (\<epsilon>, u, v) # follow u)"
  by simp+

lemma follow_dom:
  shows "follow_dom v"
  using wf
  by (auto simp add: wfP_def follow_rel.simps intro: accp_wfPD)

lemma follow_psimps:
  shows "follow v = (case m v of None \<Rightarrow> [] | Some (\<epsilon>, u) \<Rightarrow> (\<epsilon>, u, v) # follow u)"
  using follow_dom
  by (intro follow.psimps)

lemma follow_induct:
  assumes "\<And>v. (\<And>\<epsilon> u. m v = Some (\<epsilon>, u) \<Longrightarrow> P u) \<Longrightarrow> P v"
  shows "P v"
  using follow_dom assms
  by (rule follow.pinduct) simp

lemma follow_induct_2:
  assumes "\<And>v. (\<And>p. m v = Some p \<Longrightarrow> P (snd p)) \<Longrightarrow> P v"
  shows "P v"
  using assms
  by (rule follow_induct) force

definition rev_follow :: "'b \<Rightarrow> ('a, 'b) walk" where
  "rev_follow v = rev (follow v)"

lemma rev_follow_simps:
  shows "rev_follow v = (case m v of None \<Rightarrow> [] | Some (\<epsilon>, u) \<Rightarrow> rev_follow u @ [(\<epsilon>, u, v)])"
  by (simp add: rev_follow_def follow_psimps split: option.split)

(* TODO: Rename. *)
definition E :: "('a, 'b) multigraph" where
  "E \<equiv> {(\<epsilon>, u, v). m v = Some (\<epsilon>, u)}"

lemma mem_EI:
  assumes "m v = Some (\<epsilon>, u)"
  shows "(\<epsilon>, u, v) \<in> E"
  using assms
  by (simp add: E_def)

lemma mem_ED:
  assumes "e \<in> E"
  shows "m (head e) = Some (fst e, tail e)"
  using assms
  by (auto simp add: E_def head_def tail_def endpoints_def)

lemma
  shows "V E = dom m \<union> snd ` ran m"
  sorry

(* TODO: Move. *)
lemma rev_follow_non_emptyI:
  assumes "m v \<noteq> None"
  shows "rev_follow v \<noteq> []"
  using assms
  by (auto simp add: rev_follow_simps)

lemma cases_m [case_names None Some]:
  assumes "m v = None \<Longrightarrow> P v"
  assumes "\<And>\<epsilon> u. m v = Some (\<epsilon>, u) \<Longrightarrow> P v"
  shows "P v"
  using assms
  by fast

lemma walk_rev_follow:
  assumes "m v \<noteq> None"
  shows "walk E (rev_follow v) (tail (hd (rev_follow v))) v"
  using assms
proof (induct rule: follow_induct)
  case (1 v)
  show ?case
  proof (induct rule: cases_m)
    case None
    thus ?case
      using 1(2)
      by simp
  next
    case m_v_eq_Some: (Some \<epsilon> u)
    show ?case
    proof (induct rule: cases_m[of u])
      case None
      hence "rev_follow v = [(\<epsilon>, u, v)]"
        using m_v_eq_Some
        by (auto simp add: rev_follow_simps)
      thus ?case
        using m_v_eq_Some
        by (simp add: walk_singleton_iff E_def endpoints_def tail_def)
    next
      case Some
      hence "rev_follow v = rev_follow u @ [(\<epsilon>, u, v)]"
        using m_v_eq_Some
        by (auto simp add: rev_follow_simps)
      moreover hence "hd (rev_follow v) = hd (rev_follow u)"
        using Some
        by (auto simp add: hd_append rev_follow_simps)
      ultimately show ?case
        using m_v_eq_Some Some
        by (auto simp add: walk_snoc_iff tail_def endpoints_def E_def head_def dest: "1.hyps")
    qed
  qed
qed

end

locale tree = tbd
  where m = T
  for T :: "'b \<rightharpoonup> 'a \<times> 'b" +
  fixes r :: 'b
  assumes T_r_eq_None: "T r = None"
  assumes tail_last_follow_eq_r: "T v \<noteq> None \<Longrightarrow> tail (last (follow v)) = r"
begin

lemma tail_hd_rev_follow_eq_r:
  assumes "T v \<noteq> None"
  shows "tail (hd (rev_follow v)) = r"
  using assms
  by (auto simp add: rev_follow_def hd_rev intro: tail_last_follow_eq_r)

lemma unique_walk:
  assumes "walk E p r v"
  shows "p = rev_follow v"
  using assms
proof (induct arbitrary: v rule: rev_induct)
  case Nil
  thus ?case
    by (simp add: walk_Nil_iff T_r_eq_None rev_follow_simps)
next
  case (snoc e es)
  thus ?case
    by (auto simp add: walk_snoc_iff head_def tail_def endpoints_def rev_follow_simps dest: mem_ED)
qed

end

end