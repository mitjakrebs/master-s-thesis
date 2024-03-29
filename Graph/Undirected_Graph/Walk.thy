theory Walk
  imports
    Multigraph
begin

type_synonym ('a, 'b) walk = "('a, 'b) edge list"

context other
begin

inductive walk :: "('a, 'b) multigraph \<Rightarrow> ('a, 'b) walk \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  walk_Nil: "v \<in> V G \<Longrightarrow> walk G [] v v" |
  walk_Cons: "\<lbrakk> e \<in> G; u \<in> endpoints e; walk G es (other e u) v \<rbrakk> \<Longrightarrow> walk G (e # es) u v"

inductive_simps walk_Nil_iff: "walk G [] u v"
inductive_simps walk_Cons_iff: "walk G (e # es) u v"

(*
inductive walk :: "('a, 'b) multigraph \<Rightarrow> ('a, 'b) walk \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  walk_Nil: "v \<in> V G \<Longrightarrow> walk G [] v v" |
  walk_Cons: "\<lbrakk> e \<in> G; v \<in> endpoints e \<rbrakk> \<Longrightarrow> walk G [e] v (other e v)" |
  walk_Cons_Cons: "\<lbrakk> e \<in> G; u \<in> endpoints e; e' \<in> G; u \<in> endpoints e'; walk G (e' # es) u v \<rbrakk> \<Longrightarrow>
                   walk G (e # e' # es) (other e u) v"

inductive_simps walk_Nil_iff [simp]: "walk G [] u v"
inductive_simps walk_Cons_iff [simp]: "walk G [e] u v"
inductive_simps walk_Cons_Cons_iff [simp]: "walk G (e # e' # es) u v"
*)

(*
lemma walk_Cons_2:
  assumes "e \<in> G"
  assumes "v \<in> endpoints e"
  shows "walk G [e] (other e v) v"
proof -
  have "other e v \<in> endpoints e"
    using assms(2)
    by (fastforce dest: other)
  thus ?thesis
    using assms
    by (auto simp add: other_other_eq dest: walk_Cons)
qed
*)

(*
lemma walk_Cons_ConsE:
  assumes "walk G (e # e' # es) u v"
  obtains x where
    "other e x = u"
    "x \<in> endpoints e"
    "x \<in> endpoints e'"
    "walk G (e' # es) x v"
  using assms
  by auto
*)

(*
lemma walk_induct [case_names Nil Cons Cons_Cons]:
  assumes "P []"
  assumes "\<And>e. P [e]"
  assumes "\<And>e e' es. P (e' # es) \<Longrightarrow> P (e # e' # es)"
  shows "P p"
  using assms
  by (auto intro: induct_list012)

lemma walk_cases [case_names Nil Cons Cons_Cons]:
  assumes "P []"
  assumes "\<And>e. P [e]"
  assumes "\<And>e e' es. P (e # e' # es)"
  shows "P p"
  using assms
  by (auto intro: walk_induct)
*)

(*
lemma walk_tlI:
  assumes "walk G (e # es) u v"
  shows "walk G es (other e u) v"
  sorry
*)

lemma walk_singletonI:
  assumes "e \<in> G"
  assumes "v \<in> endpoints e"
  shows "walk G [e] v (other e v)"
  using assms
  by (auto simp add: walk_Cons_iff walk_Nil_iff V_def dest: other)

lemma walk_singleton_iff:
  shows "walk G [e] u v \<longleftrightarrow> e \<in> G \<and> endpoints e = {u, v}"
proof (standard, goal_cases)
  case 1
  thus ?case
    by (simp add: walk_Cons_iff walk_Nil_iff other)
next
  case 2
  hence "other e u = v"
    using other
    by (fastforce simp add: doubleton_eq_iff)
  thus ?case
    using 2
    by (blast intro: walk_singletonI)
qed

(* QQQ *)
lemma walk_appendI:
  assumes "walk G p u v"
  assumes "walk G p' v w"
  shows "walk G (p @ p') u w"
  sorry

lemma walk_revI:
  assumes "walk G p u v"
  shows "walk G (rev p) v u"
  using assms
proof (induct p arbitrary: u)
  case Nil
  thus ?case
    by (simp add: walk_Nil_iff)
next
  case (Cons e es)
  then show ?case sorry
qed

lemma set_walk_subset:
  assumes "walk G p u v"
  shows "set p \<subseteq> G"
  using assms
  by (induct p arbitrary: u) (auto simp add: walk_Cons_iff)

(*
lemma hd_walk:
  assumes "walk G p u v"
  assumes "p \<noteq> []"
  shows "u \<in> endpoints (hd p)"
  using assms
proof (induct rule: walk_cases)
  case Nil
  thus ?case
    by blast
next
  case (Cons e)
  thus ?case
    by simp
next
  case (Cons_Cons e e' es)
  thus ?case
    by (fastforce dest: other elim: walk_Cons_ConsE)
qed
*)

(*
lemma hd_walk_2:
  assumes "walk G p u v"
  assumes "p \<noteq> []"
  shows "other (hd p) u \<in> endpoints (hd p)"
  using assms
  by (fastforce dest: hd_walk other)
*)

fun walk_vertices :: "('a, 'b) walk \<Rightarrow> 'b \<Rightarrow> 'b list" where
  "walk_vertices [] v = [v]" |
  "walk_vertices (e # es) v = v # walk_vertices es (other e v)"

lemma endpoint_mem_set_walk_vertices:
  assumes "walk G p u v"
  assumes "e \<in> set p"
  assumes "x \<in> endpoints e"
  shows "x \<in> set (walk_vertices p u)"
  using assms
proof (induct arbitrary: u rule: walk_vertices.induct)
  case (1 v)
  thus ?case
    by force
next
  case (2 e es v)
  then show ?case sorry
qed

lemma set_walk_vertices_tl_subset:
  assumes "walk G (e # es) u v"
  shows "set (walk_vertices es (other e u)) \<subseteq> set (walk_vertices (e # es) u)"
  sorry

definition reachable :: "('a, 'b) multigraph \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "reachable G u v \<equiv> \<exists>p. walk G p u v"

lemma reachable_refl:
  assumes "v \<in> V G"
  shows "reachable G v v"
  using assms
  by (auto simp add: reachable_def intro: walk_Nil)

end

end