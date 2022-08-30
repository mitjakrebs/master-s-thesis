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

locale multigraph =
  fixes G :: "('a, 'b) multigraph"

locale finite_multigraph = multigraph +
  assumes finite_edges: "finite G"

lemma (in finite_multigraph) finite_vertices:
  shows "finite (V G)"
  using finite_edges
  by (simp add: V_def)

end