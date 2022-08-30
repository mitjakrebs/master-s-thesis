theory Directed_Incidence_Structure
  imports
    Incidence_Structure
    "../Directed_Graph/Directed_Graph"
begin

(*
QUESTION: Define locale Directed_Incidence_Structure, which is equal to Incidence_Structure except
that it overwrites incidence, and then show that Incidence_Structure is a sublocale of
Directed_Incidence_Structure?
*)
locale directed_incidence_structure =
  fixes incidence :: "'b \<Rightarrow> 'g \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list"
  assumes mem_incidence_imp_tail: "e \<in> set (incidence v G) \<Longrightarrow> tail e = v"

definition (in directed_incidence_structure) A :: "'g \<Rightarrow> ('a, 'b) Directed_Multigraph.multigraph" where
  "A G \<equiv> \<Union>v. set (incidence v G)"

lemma (in directed_incidence_structure) mem_incidence_iff_edge:
  shows "e \<in> set (incidence (tail e) G) \<longleftrightarrow> e \<in> A G"
  by (auto simp add: A_def dest: mem_incidence_imp_tail)

context Incidence_Structure
begin
sublocale directed_incidence_structure "\<lambda>u G. map (\<lambda>(\<epsilon>, v). (\<epsilon>, (u, v))) (incidence u G)"
proof (standard, goal_cases)
  case (1 e v G)
  thus ?case
    by (auto simp add: tail_def endpoints_def)
qed
end

locale directed_incidence_structure' = directed_incidence_structure
  where incidence = incidence
  for incidence :: "'b \<Rightarrow> 'g \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list" +
  fixes G :: 'g
begin
sublocale Directed_Multigraph.multigraph "dE G"
  .
end

end