theory Walk_Adaptor
  imports
    Multigraph_Adaptor
    "../Directed_Graph/Directed_Walk"
    "../Undirected_Graph/Walk"
begin

lemma (in huehuehue) walk_imp_walk_image_undirect:
  assumes "Directed_Walk.walk G p u v"
  shows "walk (undirect ` G) (map undirect p) u v"
  using assms
proof (induct p arbitrary: u)
  case Nil
  thus ?case
    by (auto simp add: Directed_Walk.walk_Nil_iff V_image_undirect_eq intro: walk_Nil)
next
  case (Cons e es)
  show ?case
    unfolding list.map(2)
  proof (rule walk_Cons, goal_cases)
    case 1
    show ?case
      using Cons.prems
      by (simp add: Directed_Walk.walk_Cons_iff)
  next
    case 2
    show ?case
      using tail_mem_endpoints_undirect Cons.prems
      by (fastforce simp add: Directed_Walk.walk_Cons_iff)
  next
    case 3
    show ?case
      using Cons.prems
      by (auto simp add: Directed_Walk.walk_Cons_iff head_eq_other_tail intro: Cons.hyps)
  qed
qed

end