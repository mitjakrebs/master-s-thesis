theory Directed_Multigraph
  imports
    Main
begin

type_synonym ('a, 'b) edge = "'a \<times> ('b \<times> 'b)"

type_synonym ('a, 'b) multigraph = "('a, 'b) edge set"

definition endpoints :: "('a, 'b) edge \<Rightarrow> 'b \<times> 'b" where
  "endpoints \<equiv> snd"

lemma mem_endpoints_iff:
  shows "vs \<in> endpoints ` G \<longleftrightarrow> (\<exists>\<epsilon>. (\<epsilon>, vs) \<in> G)"
  by (force simp add: endpoints_def)

definition head :: "('a, 'b) edge \<Rightarrow> 'b" where
  "head e \<equiv> snd (endpoints e)"

definition tail :: "('a, 'b) edge \<Rightarrow> 'b" where
  "tail e \<equiv> fst (endpoints e)"

lemma mem_ED:
  assumes "e \<in> G"
  shows "(tail e, head e) \<in> endpoints ` G"
  using assms
  by (simp add: head_def tail_def endpoints_def mem_endpoints_iff)

definition V :: "('a, 'b) multigraph \<Rightarrow> 'b set" where
  "V G \<equiv> head ` G \<union> tail ` G"

lemma head_mem_V:
  assumes "e \<in> G"
  shows "head e \<in> V G"
  using assms
  by (simp add: V_def)

lemma head_mem_V_2:
  assumes "(\<epsilon>, u, v) \<in> G"
  shows "v \<in> V G"
  using assms
  by (auto simp add: head_def endpoints_def dest: head_mem_V)

lemma head_mem_V_3:
  assumes "(u, v) \<in> endpoints ` G"
  shows "v \<in> V G"
  using assms
  by (auto simp add: mem_endpoints_iff dest: head_mem_V_2)

lemma tail_mem_V:
  assumes "e \<in> G"
  shows "tail e \<in> V G"
  using assms
  by (simp add: V_def)

lemma tail_mem_V_2:
  assumes "(\<epsilon>, u, v) \<in> G"
  shows "u \<in> V G"
  using assms
  by (auto simp add: tail_def endpoints_def dest: tail_mem_V)

lemma tail_mem_V_3:
  assumes "(u, v) \<in> endpoints ` G"
  shows "u \<in> V G"
  using assms
  by (auto simp add: mem_endpoints_iff dest: tail_mem_V_2)

lemma mem_VE:
  assumes "u \<in> V G"
  obtains v where
    "(u, v) \<in> endpoints ` G \<or> (v, u) \<in> endpoints ` G"
  using assms
  by (force simp add: V_def head_def tail_def endpoints_def)

locale multigraph =
  fixes G :: "('a, 'b) multigraph"

locale finite_multigraph = multigraph +
  assumes finite_edges: "finite G"

lemma (in finite_multigraph) finite_vertices:
  shows "finite (V G)"
  using finite_edges
  by (simp add: V_def)

(**)

definition to_edge :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('a, 'b) edge" where
  "to_edge v p \<equiv> (fst p, (v, snd p))"

definition incidence :: "('b \<Rightarrow> ('a \<times> 'b) list) \<Rightarrow> 'b \<Rightarrow> ('a, 'b) edge list" where
  "incidence I v \<equiv> map (to_edge v) (I v)"

(* TODO: Rename. *)
definition edges_from_fun :: "('b \<Rightarrow> ('a \<times> 'b) list) \<Rightarrow> ('a, 'b) multigraph" where
  "edges_from_fun I \<equiv> \<Union>v. set (incidence I v)"

lemma mem_edges_from_funE:
  assumes "e \<in> edges_from_fun I"
  obtains v where
    "e \<in> set (incidence I v)"
  using assms
  by (auto simp add: edges_from_fun_def)

lemma mem_edges_from_funI:
  assumes "e \<in> set (incidence I v)"
  shows "e \<in> edges_from_fun I"
  using assms
  by (auto simp add: edges_from_fun_def)

locale multigraph_2 =
  fixes I :: "'b \<Rightarrow> ('a \<times> 'b) list"
begin

lemma inj_to_edge:
  shows "inj (to_edge v)"
  by (auto simp add: to_edge_def intro: injI)

(* TODO: Move. *)
lemma inj_on_if_inj:
  assumes "inj f"
  shows "inj_on f A"
  using assms
  by (simp add: inj_on_def)

lemma tail_eq:
  assumes "e \<in> set (incidence I v)"
  shows "tail e = v"
  using assms
  by (auto simp add: incidence_def to_edge_def tail_def endpoints_def)

lemma mem_edges_from_funD:
  assumes "e \<in> edges_from_fun I"
  shows "e \<in> set (incidence I (tail e))"
  using assms
  by (auto simp add: tail_eq elim: mem_edges_from_funE)

sublocale multigraph "edges_from_fun I"
  .

end

locale finite_multigraph_2 = multigraph_2 +
  assumes finite_domain: "finite {v. I v \<noteq> []}"
begin

lemma edges_from_fun_eq:
  shows "edges_from_fun I = \<Union> ((set \<circ> incidence I) ` {v. I v \<noteq> []})"
  by (force simp add: edges_from_fun_def incidence_def)

sublocale finite_multigraph "edges_from_fun I"
proof (standard, goal_cases)
  case 1
  show ?case
    using finite_domain
    by (simp add: edges_from_fun_eq)
qed

end

end