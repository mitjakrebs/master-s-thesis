theory Multigraph_Adaptor
  imports
    "../Directed_Graph/Directed_Multigraph"
    "../Undirected_Graph/Multigraph"
begin

fun undirect :: "('a, 'b) Directed_Multigraph.edge \<Rightarrow> ('a, 'b) Multigraph.edge" where
  "undirect (\<epsilon>, u, v) = (\<epsilon>, {u, v})"

lemma
  shows
    head_mem_endpoints_undirect: "head e \<in> Multigraph.endpoints (undirect e)" and
    tail_mem_endpoints_undirect: "tail e \<in> Multigraph.endpoints (undirect e)"
proof -
  obtain \<epsilon> u v where
    "e = (\<epsilon>, u, v)"
    by (elim undirect.cases)
  thus
    "head e \<in> Multigraph.endpoints (undirect e)"
    "tail e \<in> Multigraph.endpoints (undirect e)"
    by (simp_all add: head_def tail_def Directed_Multigraph.endpoints_def Multigraph.endpoints_def)
qed

lemma endpoints_undirect_eq:
  shows "Multigraph.endpoints (undirect e) = {head e, tail e}"
proof -
  obtain \<epsilon> u v where
    "e = (\<epsilon>, u, v)"
    by (elim undirect.cases)
  thus ?thesis
    by (auto simp add: Multigraph.endpoints_def head_def tail_def Directed_Multigraph.endpoints_def)
qed

lemma (in other) tail_eq_other_head:
  shows "tail e = other (undirect e) (head e)"
proof -
  have "{head e, tail e} = {head e, other (undirect e) (head e)}"
    using endpoints_undirect_eq head_mem_endpoints_undirect
    by (fast dest: other)
  thus ?thesis
    by (auto simp add: doubleton_eq_iff)
qed

lemma (in other) head_eq_other_tail:
  shows "head e = other (undirect e) (tail e)"
proof -
  have "{head e, tail e} = {tail e, other (undirect e) (tail e)}"
    using endpoints_undirect_eq tail_mem_endpoints_undirect
    by (metis other)
  thus ?thesis
    by (auto simp add: doubleton_eq_iff)
qed

lemma mem_image_undirect_iff:
  shows "(\<epsilon>, {u, v}) \<in> undirect ` G \<longleftrightarrow> (\<epsilon>, u, v) \<in> G \<or> (\<epsilon>, v, u) \<in> G"
  by (force simp add: doubleton_eq_iff)

lemma mem_endpoints_image_undirect_iff:
  shows
    "{u, v} \<in> Multigraph.endpoints ` undirect ` G \<longleftrightarrow>
     (u, v) \<in> Directed_Multigraph.endpoints ` G \<or> (v, u) \<in> Directed_Multigraph.endpoints ` G"
  unfolding Multigraph.mem_endpoints_iff Directed_Multigraph.mem_endpoints_iff mem_image_undirect_iff
  by blast

(* TODO: Rename. *)
locale huehuehue =
  Directed_Multigraph.finite_multigraph
  where G = G +
    other
  where other = other
  for G :: "('a, 'b) Directed_Multigraph.multigraph"
    and other :: "('a, 'b) Multigraph.edge \<Rightarrow> 'b \<Rightarrow> 'b"
begin
sublocale Multigraph.finite_multigraph other "undirect ` G"
proof (standard, goal_cases)
  case (1 e)
  thus ?case
    by (auto simp add: Multigraph.endpoints_def)
next
  case 2
  show ?case
    using finite_edges
    by simp
qed
  
end

lemma (in huehuehue) V_image_undirect_eq:
  shows "Multigraph.V (undirect ` G) = Directed_Multigraph.V G"
proof (standard, goal_cases)
  case 1
  show ?case
  proof (standard, goal_cases)
    case (1 u)
    then obtain v where
      "{u, v} \<in> Multigraph.endpoints ` undirect ` G"
      by (elim mem_VE)
    thus ?case
      by (auto simp add: mem_endpoints_image_undirect_iff intro: head_mem_V_3 tail_mem_V_3)
  qed
next
  case 2
  show ?case
  proof (standard, goal_cases)
    case (1 u)
    then obtain v where
      "(u, v) \<in> Directed_Multigraph.endpoints ` G \<or> (v, u) \<in> Directed_Multigraph.endpoints ` G"
      by (elim Directed_Multigraph.mem_VE)
    thus ?case
      by (auto simp add: mem_endpoints_image_undirect_iff[symmetric] intro: mem_VI_2)
  qed
qed

end