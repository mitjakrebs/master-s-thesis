theory Multigraph
  imports
    Main
begin

type_synonym ('a, 'b) edge = "'a \<times> 'b set"

type_synonym ('a, 'b) multigraph = "('a, 'b) edge set"

definition endpoints :: "('a, 'b) edge \<Rightarrow> 'b set" where
  "endpoints \<equiv> snd"

lemma mem_endpoints_iff:
  shows "e \<in> endpoints ` G \<longleftrightarrow> (\<exists>\<epsilon>. (\<epsilon>, e) \<in> G)"
  by (force simp add: endpoints_def)

definition V :: "('a, 'b) multigraph \<Rightarrow> 'b set" where
  "V G \<equiv> \<Union> (endpoints ` G)"

lemma mem_VI:
  assumes "(\<epsilon>, {u, v}) \<in> G"
  shows
    "u \<in> V G"
    "v \<in> V G"
  using assms
  by (force simp add: V_def endpoints_def)+

lemma
  assumes "G \<subseteq> G'"
  shows "V G \<subseteq> V G'"
  using assms
  by (auto simp add: V_def)

definition is_multiple_edge :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> bool" where
  "is_multiple_edge G vs \<equiv> \<exists>\<epsilon> \<epsilon>'. \<epsilon> \<noteq> \<epsilon>' \<and> (\<epsilon>, vs) \<in> G \<and> (\<epsilon>', vs) \<in> G"

(* TODO: Rename. *)
locale other =
  fixes other :: "('a, 'b) edge \<Rightarrow> 'b \<Rightarrow> 'b"
  assumes other: "v \<in> endpoints e \<Longrightarrow> endpoints e = {v, other e v}"

lemma (in other) other_other_eq:
  assumes "v \<in> endpoints e"
  shows "other e (other e v) = v"
  using assms
proof -
  have "other e v \<in> endpoints e"
    using assms
    by (fastforce dest: other)
  thus ?thesis
    using assms
    by (fastforce dest: other)
qed

(* QUESTION: Do we need that the edge identifiers are unique? *)
locale multigraph = other
  where other = other
  for other :: "('a, 'b) edge \<Rightarrow> 'b \<Rightarrow> 'b" +
  fixes G :: "('a, 'b) multigraph"
  assumes endpoints_non_empty: "e \<in> G \<Longrightarrow> endpoints e \<noteq> {}"

lemma (in multigraph) no_hyperedges:
  assumes "e \<in> G"
  obtains u v where
    "endpoints e = {u, v}"
proof -
  obtain u where
    "u \<in> endpoints e"
    using assms endpoints_non_empty
    by fastforce
  thus ?thesis
    by (fastforce dest: other that)
qed

locale finite_multigraph = multigraph +
  assumes finite_edges: "finite G"

lemma (in finite_multigraph) finite_vertices:
  shows "finite (V G)"
  using finite_edges
  by (auto simp add: V_def elim: no_hyperedges)

(* TODO: Move. *)
definition idk :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) multigraph" where
  "idk G X Y \<equiv> {e \<in> G. endpoints e \<subseteq> X \<union> Y \<and> endpoints e \<inter> X \<noteq> {} \<and> endpoints e \<inter> Y \<noteq> {}}"

definition idk_2 :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) multigraph" where
  "idk_2 G X \<equiv> idk G X X"

definition idk_3 :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) multigraph" where
  "idk_3 G \<equiv> idk G (V G)"

lemma mem_endpoints_idk_3I:
  assumes "x \<in> X"
  assumes "{x, y} \<in> endpoints ` G"
  shows "{x, y} \<in> endpoints ` idk_3 G X"
  using assms
  sorry

definition idk_4 :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) multigraph" where
  "idk_4 G X \<equiv> G - idk_3 G X"

lemma V_idk_4_subset:
  shows "V (idk_4 G X) \<subseteq> V G - X"
  sorry

(* TODO: Requires biconnected G. *)
lemma V_idk_4_eq:
  shows "V (idk_4 G X) = V G - X"
  sorry

lemma mem_endpoints_idk_4I:
  assumes "{x, y} \<in> endpoints ` G"
  assumes "x \<notin> X"
  assumes "y \<notin> X"
  shows "{x, y} \<in> endpoints ` idk_4 G X"
  using assms
  sorry

(* TODO: Move. *)
(* TODO: Generalize. *)
definition E :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) multigraph" where
  "E G X \<equiv> {e \<in> G. endpoints e \<inter> X \<noteq> {}}"

lemma E_subset:
  shows "E G X \<subseteq> G"
  by (simp add: E_def)

lemma E_empty_set_eq:
  shows "E G {} = {}"
  by (simp add: E_def)

lemma (in multigraph) E_V_eq:
  shows "E G (V G) = G"
proof (standard, goal_cases)
  case 1
  show ?case
    using E_subset
    .
next
  case 2
  show ?case
  proof
    fix e
    assume "e \<in> G"
    thus "e \<in> E G (V G)"
      unfolding E_def V_def
      by (blast dest: endpoints_non_empty)
  qed
qed

lemma E_union_eq:
  shows "E G (X \<union> Y) = E G X \<union> E G Y"
  by (auto simp add: E_def)

lemma V_E_superset:
  assumes "X \<subseteq> V G"
  shows "X \<subseteq> V (E G X)"
  using assms
  by (fastforce simp add: V_def E_def)

lemma mem_endpoints_EI:
  assumes "x \<in> X"
  assumes "{x, y} \<in> endpoints ` G"
  shows "{x, y} \<in> endpoints ` E G X"
  using assms
  sorry

end