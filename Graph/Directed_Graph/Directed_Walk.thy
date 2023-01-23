theory Directed_Walk
  imports
    Directed_Multigraph
    Graph_Theory.Rtrancl_On
begin

type_synonym ('a, 'b) walk = "('a, 'b) edge list"

inductive walk :: "('a, 'b) multigraph \<Rightarrow> ('a, 'b) walk \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  walk_Nil: "v \<in> V G \<Longrightarrow> walk G [] v v" |
  walk_Cons: "\<lbrakk> e \<in> G; walk G es (head e) v \<rbrakk> \<Longrightarrow> walk G (e # es) (tail e) v"

inductive_simps walk_Nil_iff: "walk G [] u v"
inductive_simps walk_Cons_iff: "walk G (e # es) u v"

lemma walk_iff:
  assumes "p \<noteq> []"
  shows "walk G p u v \<longleftrightarrow> hd p \<in> G \<and> walk G (tl p) (head (hd p)) v \<and> tail (hd p) = u"
  using assms
  by (cases p) (auto simp add: walk_Cons_iff)

lemma walk_singletonI:
  assumes "e \<in> G"
  shows "walk G [e] (tail e) (head e)"
  using assms
  by (auto simp add: walk_Cons_iff walk_Nil_iff dest: head_mem_V)

lemma walk_singleton_iff:
  shows "walk G [e] u v \<longleftrightarrow> e \<in> G \<and> endpoints e = (u, v)"
  by (auto simp add: walk_Cons_iff tail_def head_def walk_Nil_iff dest: head_mem_V)

(*
inductive walk :: "('a, 'b) multigraph \<Rightarrow> ('a, 'b) walk \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  walk_Nil: "v \<in> V G \<Longrightarrow> walk G [] v v" |
  walk_Cons: "e \<in> G \<Longrightarrow> walk G [e] (tail e) (head e)" |
  walk_Cons_Cons: "\<lbrakk> e \<in> G; e' \<in> G; tail e' = head e; walk G (e' # es) (tail e') v \<rbrakk> \<Longrightarrow>
                   walk G (e # e' # es) (tail e) v"

inductive_simps walk_Nil_iff [simp]: "walk G [] u v"
inductive_simps walk_Cons_iff [simp]: "walk G [e] u v"
inductive_simps walk_Cons_Cons_iff [simp]: "walk G (e # e' # es) u v"
*)

lemma hd_vertex_mem_V:
  assumes "walk G p u v"
  shows "u \<in> V G"
  using assms
  by (cases p) (auto simp add: walk_Nil_iff walk_Cons_iff dest: tail_mem_V)

lemma last_vertex_mem_V:
  assumes "walk G p u v"
  shows "v \<in> V G"
  using assms
  by (induct p arbitrary: u) (auto simp add: walk_Nil_iff walk_Cons_iff dest: tail_mem_V)

fun walk_vertices :: "('a, 'b) walk \<Rightarrow> 'b \<Rightarrow> 'b list" where
  "walk_vertices [] v = [v]" |
  "walk_vertices (e # es) _ = tail e # walk_vertices es (head e)"

lemma walk_vertices_non_empty:
  shows "walk_vertices p v \<noteq> []"
  by (cases p) simp_all

lemma walk_vertices_cong:
  shows "walk_vertices p v = (if p = [] then [v] else map tail p @ [head (last p)])"
  by (induct p arbitrary: v) simp_all

lemma walk_vertices_cong_2:
  assumes "walk G p u v"
  shows "walk_vertices p u = (if p = [] then [u] else tail (hd p) # map head p)"
  using assms
  by (induct p arbitrary: u) (auto simp add: walk_iff)

lemma dinstinct_walk_vertices_imp_distinct:
  assumes "distinct (walk_vertices p u)"
  shows "distinct p"
  using assms
  by (cases p) (auto simp add: walk_vertices_cong distinct_map)

definition hd_vertex :: "('a, 'b) walk \<Rightarrow> 'b \<Rightarrow> 'b" where
  "hd_vertex p v \<equiv> hd (walk_vertices p v)"

definition last_vertex :: "('a, 'b) walk \<Rightarrow> 'b \<Rightarrow> 'b" where
  "last_vertex p v \<equiv> last (walk_vertices p v)"

lemma hd_vertex_eq:
  assumes "walk G p u v"
  shows "hd_vertex p u = u"
  using assms
  by (cases p) (simp_all add: walk_Cons_iff hd_vertex_def)

lemma last_vertex_eq:
  assumes "walk G p u v"
  shows "last_vertex p u = v"
  using assms
proof (induct p arbitrary: u)
  case Nil
  thus ?case
    by (simp add: walk_Nil_iff last_vertex_def)
next
  case (Cons e es)
  thus ?case
    using walk_vertices_non_empty
    by (fastforce simp add: walk_Cons_iff last_vertex_def)
qed

lemma walk_append_iff:
  shows "walk G (p @ p') u v \<longleftrightarrow> walk G p u (last_vertex p u) \<and> walk G p' (last_vertex p u) v"
proof (induct p arbitrary: u)
  case Nil
  thus ?case
    by (auto simp add: walk_Nil_iff last_vertex_def dest: hd_vertex_mem_V)
next
  case (Cons e es)
  thus ?case
    using walk_vertices_non_empty
    by (fastforce simp add: walk_Cons_iff last_vertex_def)
qed

lemma walk_snoc_iff:
  shows "walk G (p @ [e]) u v \<longleftrightarrow> walk G p u (tail e) \<and> e \<in> G \<and> head e = v"
  by (fastforce simp add: walk_append_iff walk_singleton_iff tail_def head_def last_vertex_eq)

lemma walk_snocD:
  assumes "walk G (p @ [e]) u v"
  shows
    "walk G p u (tail e)"
    "e \<in> G"
    "head e = v"
  using assms
  by (simp_all add: walk_snoc_iff)

(* TODO: Beautify. *)
lemma walk_vertices_snoc:
  assumes "walk G (es @ [e]) u v"
  shows "walk_vertices (es @ [e]) x = walk_vertices es (tail e) @ [head e]"
  using assms
  by (metis (no_types, lifting) append_self_conv2 last_vertex_def last_vertex_eq list.simps(9) map_append snoc_eq_iff_butlast walk_snoc_iff walk_vertices_cong)

definition reachable :: "('a, 'b) multigraph \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "reachable G u v \<equiv> (u, v) \<in> rtrancl_on (V G) (endpoints ` G)"

lemma reachableE:
  assumes "reachable G u v"
  obtains p where
    "walk G p u v"
  using assms
  unfolding reachable_def
proof (induct rule: rtrancl_on.induct)
  case (rtrancl_on_refl v)
  thus ?case
    by (fast intro: walk_Nil)
next
  case (rtrancl_on_into_rtrancl_on u v w)
  thus ?case
    using walk_append_iff walk_singleton_iff last_vertex_eq
    by fastforce
qed

lemma reachableI:
  assumes "walk G p u v"
  shows "reachable G u v"
  using assms
  unfolding reachable_def
proof (induct arbitrary: v rule: rev_induct)
  case Nil
  thus ?case
    by (simp add: walk_Nil_iff)
next
  case (snoc e es)
  show ?case
  proof (rule rtrancl_on_into_rtrancl_on[where ?b = "tail e"], goal_cases)
    case 1
    show ?case
      using snoc.prems
      by (auto simp add: walk_snoc_iff intro: snoc.hyps)
  next
    case 2
    thus ?case
      using snoc.prems
      by (auto simp add: walk_snoc_iff dest: mem_ED)
  next
    case 3
    then show ?case
      using snoc.prems
      by (fast dest: last_vertex_mem_V)
  qed
qed

end