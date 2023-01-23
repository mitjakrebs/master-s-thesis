(* TODO Move. *)
(* TODO Rename. *)
theory Tbd
  imports
    Directed_Walk
begin

(* TODO: Rename. *)
definition edges_from_map :: "('b \<rightharpoonup> 'a \<times> 'b) \<Rightarrow> ('a, 'b) multigraph" where
  "edges_from_map m \<equiv> {(\<epsilon>, u, v). m v = Some (\<epsilon>, u)}"

lemma mem_edges_from_mapI:
  assumes "m v = Some (\<epsilon>, u)"
  shows "(\<epsilon>, u, v) \<in> edges_from_map m"
  using assms
  by (simp add: edges_from_map_def)

lemma mem_edges_from_mapD:
  assumes "e \<in> edges_from_map m"
  shows "m (head e) = Some (fst e, tail e)"
  using assms
  by (auto simp add: edges_from_map_def head_def tail_def endpoints_def)

lemma mem_edges_from_mapD_2:
  assumes "(\<epsilon>, u, v) \<in> edges_from_map m"
  shows "m v = Some (\<epsilon>, u)"
  using assms
  by (auto simp add: head_def tail_def endpoints_def dest: mem_edges_from_mapD)

lemma edges_from_map_subset_if_map_le:
  assumes "m1 \<subseteq>\<^sub>m m2"
  shows "edges_from_map m1 \<subseteq> edges_from_map m2"
proof (standard, goal_cases)
  case (1 e)
  let ?\<epsilon> = "fst e"
  let ?u = "tail e"
  let ?v = "head e"
  have "m1 ?v = Some (?\<epsilon>, ?u)"
    using 1
    by (blast dest: mem_edges_from_mapD)
  hence "m2 ?v = Some (?\<epsilon>, ?u)"
    using assms
    by (simp add: map_le_def dom_def)
  thus ?case
    by (auto simp add: head_def tail_def endpoints_def dest: mem_edges_from_mapI)
qed

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

lemma follow_simps:
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
  by (simp add: rev_follow_def follow_simps split: option.split)

lemma
  shows "V (edges_from_map m) = dom m \<union> snd ` ran m"
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
  shows "walk (edges_from_map m) (rev_follow v) (tail (hd (rev_follow v))) v"
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
        by (simp add: walk_singleton_iff edges_from_map_def endpoints_def tail_def)
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
        by (auto simp add: walk_snoc_iff tail_def endpoints_def edges_from_map_def head_def dest: "1.hyps")
    qed
  qed
qed

lemma
  assumes "walk_vertices (rev_follow v) v = vs @ u # vs'"
  shows "walk_vertices (rev_follow u) u = vs @ [u]"
  using assms
proof (induct vs' arbitrary: v rule: rev_induct)
  case Nil
  then show ?case sorry
next
  case (snoc x xs)
  then show ?case sorry
qed

lemma m_eq_SomeD:
  assumes "m v = Some (\<epsilon>, u)"
  shows "v \<notin> set (walk_vertices (rev_follow u) u)"
proof
  assume "v \<in> set (walk_vertices (rev_follow u) u)"
  then obtain vs vs' where
    "walk_vertices (rev_follow u) u = vs @ v # vs'"
    by (fast dest: split_list)
  hence
    "walk_vertices (rev_follow v) v = vs @ v # vs @ [v]"
    "walk_vertices (rev_follow v) v = vs @ [v]"
    sorry
  thus False
    by force
qed

lemma distinct_walk_vertices_rev_follow:
  shows "distinct (walk_vertices (rev_follow v) v)"
proof (induct v rule: follow_induct)
  case (1 v)
  show ?case
  proof (cases rule: cases_m[of v])
    case None
    thus ?thesis
      by (simp add: rev_follow_simps)
  next
    case (Some \<epsilon> u)
    hence "walk_vertices (rev_follow v) v = walk_vertices (rev_follow u) u @ [v]"
      using walk_rev_follow
      by (fastforce simp add: rev_follow_simps walk_vertices_snoc tail_def head_def endpoints_def)
    thus ?thesis
      using Some
      by (fastforce dest: m_eq_SomeD intro: "1.hyps")
  qed
qed

lemma distinct_rev_follow:
  shows "distinct (rev_follow v)"
  using distinct_walk_vertices_rev_follow
  by (intro dinstinct_walk_vertices_imp_distinct)

lemma unique_walk_2:
  assumes "walk (edges_from_map m) p u v"
  shows "rev_follow u @ p = rev_follow v"
  using assms
proof (induct p arbitrary: v rule: rev_induct)
  case Nil
  thus ?case
    by (simp add: walk_Nil_iff)
next
  case (snoc e es)
  thus ?case
    by
      (auto
        simp add: walk_snoc_iff head_def tail_def endpoints_def rev_follow_simps
        dest: mem_edges_from_mapD)
qed

lemma unique_walk_3:
  assumes "walk (edges_from_map m) p1 u v"
  assumes "walk (edges_from_map m) p2 v w"
  assumes "walk (edges_from_map m) p u w"
  shows "p1 @ p2 = p"
proof -
  have "rev_follow w = rev_follow u @ p1 @ p2"
    using assms(1, 2)
    by (simp add: unique_walk_2[symmetric])
  thus ?thesis
    using assms(3)
    by (simp add: unique_walk_2[symmetric])
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

lemma walk_rev_follow:
  assumes "T v \<noteq> None"
  shows "walk (edges_from_map T) (rev_follow v) r v"
  using assms
  by (auto simp add: tail_hd_rev_follow_eq_r[symmetric] intro: walk_rev_follow)

lemma unique_walk:
  assumes "walk (edges_from_map T) p r v"
  shows "p = rev_follow v"
  using assms
proof (induct arbitrary: v rule: rev_induct)
  case Nil
  thus ?case
    by (simp add: walk_Nil_iff T_r_eq_None rev_follow_simps)
next
  case (snoc e es)
  thus ?case
    by
      (auto
        simp add: walk_snoc_iff head_def tail_def endpoints_def rev_follow_simps
        dest: mem_edges_from_mapD)
qed

end

end