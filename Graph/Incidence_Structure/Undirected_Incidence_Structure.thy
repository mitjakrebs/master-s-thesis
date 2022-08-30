theory Undirected_Incidence_Structure
  imports
    Incidence_Structure
    "../Undirected_Graph/Undirected_Graph"
begin

locale undirected_incidence_structure =
  fixes incidence :: "'b \<Rightarrow> 'g \<Rightarrow> ('a, 'b) edge list"
  assumes mem_incidence_imp_endpoint: "e \<in> set (incidence v G) \<Longrightarrow> v \<in> endpoints e"

definition (in undirected_incidence_structure) E :: "'g \<Rightarrow> ('a, 'b) multigraph" where
  "E G \<equiv> \<Union>v. set (incidence v G)"

lemma (in undirected_incidence_structure) endpoints_non_empty:
  assumes "e \<in> set (incidence v G)"
  shows "endpoints e \<noteq> {}"
  using assms
  by (auto dest: mem_incidence_imp_endpoint)

context Incidence_Structure
begin
sublocale undirected_incidence_structure "\<lambda>u G. map (\<lambda>(\<epsilon>, v). (\<epsilon>, {u, v})) (incidence u G)"
proof (standard, goal_cases)
  case (1 e v G)
  thus ?case
    by fastforce
qed
end

locale undirected_incidence_structure_2 =
  undirected_incidence_structure
  where incidence = incidence +
    other
  where other = other
  for incidence :: "'b \<Rightarrow> 'g \<Rightarrow> ('a, 'b) edge list"
    and other :: "('a, 'b) edge \<Rightarrow> 'b \<Rightarrow> 'b"

locale undirected_incidence_structure_2' = undirected_incidence_structure_2
  where incidence = incidence
  for incidence :: "'b \<Rightarrow> 'g \<Rightarrow> ('a, 'b) edge list" +
  fixes G :: 'g
begin
sublocale multigraph other "E G"
proof (standard, goal_cases)
  case (1 e)
  thm E_def
  then show ?case sorry
qed
end

end