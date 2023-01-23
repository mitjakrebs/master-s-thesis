theory Connectivity
  imports
    Walk
begin

(* TODO *)
definition connected :: "('a, 'b) multigraph \<Rightarrow> bool" where
  "connected G \<equiv> True"

locale connected_multigraph = finite_multigraph +
  assumes connected: "connected G"

(* TODO *)
definition biconnected :: "('a, 'b) multigraph \<Rightarrow> bool" where
  "biconnected G \<equiv> True"

locale biconnected_multigraph = finite_multigraph +
  assumes biconnected: "biconnected G"

(**)
(* QUESTION: Define via tbd? *)
definition (in other) connected_component where
  "connected_component G u = {v. reachable G u v}"

(* TODO: Rename. *)
lemma (in other) connected_component_refl:
  assumes "v \<in> V G"
  shows "v \<in> connected_component G v"
  using assms
  by (auto simp add: connected_component_def intro: reachable_refl)

lemma (in other) connected_component_non_empty:
  assumes "v \<in> V G"
  shows "connected_component G v \<noteq> {}"
  using assms
  by (auto intro: connected_component_refl)

lemma (in other) connected_component_subset:
  shows "connected_component G v \<subseteq> V G"
  sorry

(* QUESTION: Allow {} by removing v\<in>V G? *)
definition (in other) connected_components where
  "connected_components G \<equiv> {C. \<exists>v\<in>V G. C = connected_component G v}"

lemma (in other) connected_components_image_cong:
  shows "connected_components G = connected_component G ` V G"
  by (auto simp add: connected_components_def)

lemma (in other) connected_component_non_empty_2:
  assumes "C \<in> connected_components G"
  shows "C \<noteq> {}"
  using assms
  by (auto simp add: connected_components_def dest: connected_component_non_empty)

lemma (in other) connected_componentE:
  assumes "C \<in> connected_components G"
  obtains v where
    "connected_component G v = C"
  using assms
  by (auto simp add: connected_components_image_cong)

lemma (in other) connected_component_subset_2:
  assumes "C \<in> connected_components G"
  shows "C \<subseteq> V G"
  using assms connected_component_subset
  by (auto simp add: connected_components_def)

lemma (in other)
  assumes "C \<in> connected_components G"
  assumes "u \<in> C"
  assumes "{u, v} \<in> endpoints ` G"
  shows "v \<in> C"
  sorry

(* TODO: Rename. *)
lemma (in other) connected_component_1:
  assumes "C \<in> connected_components (idk_4 G X)"
  assumes "u \<in> C"
  assumes "{u, v} \<in> endpoints ` G"
  shows "v \<in> C \<union> X"
  sorry

lemma (in other) connected_components_disjoint:
  assumes "C1 \<in> connected_components G"
  assumes "C2 \<in> connected_components G"
  assumes "C2 \<noteq> C1"
  shows "C1 \<inter> C2 = {}"
  sorry

definition (in other) connected' :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> bool" where
  "connected' G X \<equiv> X \<subseteq> V G \<and> (\<forall>u v. u \<in> X \<and> v \<in> X \<and> v \<noteq> u \<longrightarrow> reachable (idk_2 G X) u v)"

lemma (in other) connected'_empty:
  shows "connected' G {}"
  by (simp add: connected'_def)

lemma (in other) connected'_singleton:
  assumes "v \<in> V G"
  shows "connected' G {v}"
  using assms
  by (simp add: connected'_def)

(*
definition (in other) connected' :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> bool" where
  "connected' G X \<equiv> X \<noteq> {} \<and> (\<forall>u v. u \<in> X \<and> v \<in> X \<longrightarrow> reachable (idk_2 G X) u v)"
*)

(*
lemma (in other) connected'D:
  assumes "connected' G X"
  shows
    "X \<noteq> {}"
    "\<forall>u v. u \<in> X \<and> v \<in> X \<longrightarrow> reachable (idk_2 G X) u v"
  using assms
  by (simp_all add: connected'_def)
*)

(*
lemma (in other) connected'I:
  assumes "X \<noteq> {}"
  assumes "\<forall>u v. u \<in> X \<and> v \<in> X \<longrightarrow> reachable (idk_2 G X) u v"
  shows "connected' G X"
  using assms
  by (simp add: connected'_def)
*)

lemma (in other) connected'_subset_connected_component:
  assumes "connected' G X"
  obtains C where
    "C \<in> connected_components G"
    "X \<subseteq> C"
  sorry

lemma (in other) connected'_subset:
  assumes "connected' G X"
  shows "X \<subseteq> V G"
  using assms
  by (blast elim: connected'_subset_connected_component dest: connected_component_subset_2)

(* QUESTION: Generalize to arbitrary walks in idk_2 (X \<union> Y)? *)
lemma (in other) connected'_2:
  assumes "connected' G X"
  assumes "x \<in> X"
  assumes "connected' G Y"
  assumes "y \<in> Y"
  assumes "(\<epsilon>, {x, y}) \<in> G"
  shows "connected' G (X \<union> Y)"
  sorry

lemma (in other) connected'_3:
  assumes "connected' G X"
  assumes "x \<in> X"
  assumes "connected' G Y"
  assumes "y \<in> Y"
  assumes "{x, y} \<in> endpoints ` G"
  shows "connected' G (X \<union> Y)"
  sorry

lemma (in other) connected'_1:
  assumes "connected' G X"
  assumes "X \<inter> Y = {}"
  shows "connected' (idk_4 G Y) X"
  sorry

(* QUESTION: Generalize to arbitrary walks? *)
(*
lemma (in other) connected'_not_connected_componentE:
  assumes "connected' G X"
  assumes "X \<notin> connected_components G"
  obtains x y where
    "x \<in> X"
    "{x, y} \<in> endpoints ` idk_2 G (connected_component G x)"
    "y \<in> connected_component G x"
    "y \<notin> X"
  sorry
*)

(*
lemma (in other) connected'_not_connected_componentE_2:
  assumes "connected' G X"
  assumes "X \<notin> connected_components G"
  obtains x y where
    "x \<in> X"
    "{x, y} \<in> endpoints ` G"
    "y \<in> V G"
    "y \<notin> X"
  using assms idk_2_subset connected_component_subset
  by (blast elim: connected'_not_connected_componentE)
*)

lemma (in other) connected_component_10:
  assumes "C \<in> connected_components (idk_4 G X)"
  shows "V (E G C) \<subseteq> C \<union> X"
  sorry

lemma (in other) connected'_99:
  assumes "connected' G Y"
  assumes "connected' G (X \<union> Y)"
  assumes "connected' G (Y \<union> Z)"
  shows "connected' G (X \<union> Y \<union> Z)"
  using assms
  sorry

lemma (in other) connected'_100:
  assumes "connected' G X"
  assumes "finite \<Y>"
  assumes "\<forall>Y\<in>\<Y>. connected' G Y"
  assumes "\<forall>Y\<in>\<Y>. \<exists>x\<in>X. \<exists>y\<in>Y. {x, y} \<in> endpoints ` G"
  shows "connected' G (X \<union> \<Union> \<Y>)"
  using assms(2-)
proof (induct \<Y> rule: finite.induct)
  case emptyI
  show ?case
    using assms(1)
    by simp
next
  case (insertI \<Y> Y)
  have "connected' G (Y \<union> X)"
  proof -
    have
      "connected' G Y"
      "\<exists>x\<in>X. \<exists>y\<in>Y. {x, y} \<in> endpoints ` G"
      using insertI.prems
      by blast+
    thus ?thesis
      using assms(1)
      by (blast intro: connected'_3)
  qed
  moreover have "connected' G (X \<union> \<Union> \<Y>)"
  proof -
    have
      "\<forall>Y\<in>\<Y>. connected' G Y"
      "\<forall>Y\<in>\<Y>. \<exists>x\<in>X. \<exists>y\<in>Y. {x, y} \<in> endpoints ` G"
      using insertI.prems
      by blast+
    thus ?thesis
      using assms(1)
      by (intro insertI.hyps)
  qed
  ultimately show ?case
    using assms(1)
    by (auto simp add: Un_assoc Un_left_commute dest: connected'_99)
qed

lemma (in other) connected_component_71:
  assumes "C \<in> connected_components G"
  assumes "v \<in> C"
  shows "connected_component G v = C"
proof -
  have "v \<in> V G"
    using assms
    by (fast dest: connected_component_subset_2)
  thus ?thesis
    using assms
    by
      (fastforce
        simp add: connected_components_image_cong
        dest: connected_components_disjoint
        intro: connected_component_refl)
qed

lemma (in other) connected_component_72:
  assumes "C \<in> connected_components G"
  assumes "u \<in> C"
  assumes "v \<in> C"
  obtains p where
    "walk (idk_2 G C) p u v"
  sorry

lemma (in other) connected'_supergraph:
  assumes "G \<subseteq> G'"
  assumes "connected' G X"
  shows "connected' G' X"
  using assms
  sorry

end