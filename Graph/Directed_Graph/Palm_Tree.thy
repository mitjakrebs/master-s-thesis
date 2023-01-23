theory Palm_Tree
  imports
    "../Adaptors/Walk_Adaptor"
    "../Undirected_Graph/Connectivity"
    Tbd
begin

context tree
begin

definition tree_arc :: "('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool" where
  "tree_arc e \<equiv> T (head e) = Some (fst e, tail e)"

lemma tree_arc_iff_edge:
  shows "tree_arc e \<longleftrightarrow> e \<in> (edges_from_map T)"
  by (auto simp add: tree_arc_def Directed_Multigraph.head_def Directed_Multigraph.tail_def Directed_Multigraph.endpoints_def edges_from_map_def)

definition tree_arc' :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<rightarrow>" 40) where
  "tree_arc' u v \<equiv> \<exists>\<epsilon>. tree_arc (\<epsilon>, u, v)"

lemma tree_arc'I:
  assumes "tree_arc e"
  shows "tail e \<rightarrow> head e"
proof -
  have "tree_arc (fst e, tail e, head e)"
    using assms
    by (simp add: head_def tail_def Directed_Multigraph.endpoints_def)
  thus ?thesis
    by (auto simp add: tree_arc'_def)
qed

lemma tree_arc'I_2:
  assumes "T v = Some (\<epsilon>, u)"
  shows "u \<rightarrow> v"
  using assms
  by (simp add: tree_arc'_def tree_arc_def head_def tail_def Directed_Multigraph.endpoints_def)

lemma tree_arc'E:
  assumes "u \<rightarrow> v"
  obtains \<epsilon> where
    "tree_arc (\<epsilon>, u, v)"
  using assms
  by (auto simp add: tree_arc'_def)

lemma tree_arc'_iff_mem_endpoints:
  shows "u \<rightarrow> v \<longleftrightarrow> (u, v) \<in> Directed_Multigraph.endpoints ` (edges_from_map T)"
  by (simp add: tree_arc'_def tree_arc_iff_edge Directed_Multigraph.mem_endpoints_iff)

lemma
  assumes "u \<rightarrow> v"
  shows
    tail_tree_arc'_mem_V: "u \<in> Directed_Multigraph.V (edges_from_map T)" and
    head_tree_arc'_mem_V: "v \<in> Directed_Multigraph.V (edges_from_map T)"
  using assms
  by (auto simp add: tree_arc'_iff_mem_endpoints intro: head_mem_V_3 tail_mem_V_3)

lemma no_loop:
  assumes "u \<rightarrow> v"
  shows "v \<noteq> u"
proof (standard, goal_cases)
  case 1
  obtain e where
    "e \<in> edges_from_map T"
    "Directed_Multigraph.endpoints e = (u, v)"
    using assms
    by (auto simp add: tree_arc'_iff_mem_endpoints)
  hence "walk (edges_from_map T) [e] u v"
    by (simp add: walk_singleton_iff)
  thus ?case
    using 1
    by (blast dest: unique_walk_3)
qed

(* TODO: We may have to require that both u and v are vertices. *)
definition tree_path :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<rightarrow>\<^sup>*" 40) where
  "tree_path u v \<equiv> (u, v) \<in> {(u, v). u \<rightarrow> v}\<^sup>*"

lemma tree_path_if_tree_arc':
  assumes "u \<rightarrow> v"
  shows "u \<rightarrow>\<^sup>* v"
  using assms
  by (auto simp add: tree_path_def)

lemma tree_path_refl:
  shows "u \<rightarrow>\<^sup>* u"
  by (simp add: tree_path_def)

lemma tree_path_trans:
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "v \<rightarrow>\<^sup>* w"
  shows "u \<rightarrow>\<^sup>* w"
  using assms
  by (simp add: tree_path_def)

lemma tree_path_imp_reachable:
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "u \<in> Directed_Multigraph.V (edges_from_map T)"
  shows "reachable (edges_from_map T) u v"
  using assms
  unfolding tree_path_def reachable_def
proof (induct rule: rtrancl.induct)
  case (rtrancl_refl v)
  thus ?case
    by blast
next
  case (rtrancl_into_rtrancl u v w)
  show ?case
  proof (rule rtrancl_on_into_rtrancl_on[where ?b = v], goal_cases)
    case 1
    show ?case
      using rtrancl_into_rtrancl.prems
      by (intro rtrancl_into_rtrancl.hyps(2))
  next
    case 2
    show ?case
      using rtrancl_into_rtrancl.hyps(3)
      by (simp add: tree_arc'_iff_mem_endpoints)
  next
    case 3
    show ?case
      using rtrancl_into_rtrancl.hyps(3)
      by (auto simp add: tree_arc'_iff_mem_endpoints intro: head_mem_V_3)
  qed
qed

lemma tree_path_if_reachable:
  assumes "reachable (edges_from_map T) u v"
  shows "u \<rightarrow>\<^sup>* v"
  using assms
  unfolding reachable_def tree_path_def
proof (induct rule: rtrancl_on.induct)
  case (rtrancl_on_refl v)
  thus ?case
    by simp
next
  case (rtrancl_on_into_rtrancl_on u v w)
  thus ?case
    by (simp add: tree_arc'_iff_mem_endpoints)
qed

lemma tree_path_imp_walk:
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "u \<in> Directed_Multigraph.V (edges_from_map T)"
  obtains p where
    "walk (edges_from_map T) p u v"
  using assms
  by (blast dest: tree_path_imp_reachable elim: reachableE)

lemma tree_path_if_walk:
  assumes "walk (edges_from_map T) p u v"
  shows "u \<rightarrow>\<^sup>* v"
  using assms
  by (intro reachableI tree_path_if_reachable)

definition D :: "'b \<Rightarrow> 'b set" where
  "D u \<equiv> {v. u \<rightarrow>\<^sup>* v}"

lemma mem_D_iff_tree_path:
  shows "v \<in> D u \<longleftrightarrow> u \<rightarrow>\<^sup>* v"
  by (simp add: D_def)

(* TODO: Rename. *)
lemma D_refl:
  shows "v \<in> D v"
  using tree_path_refl
  by (simp add: mem_D_iff_tree_path)

lemma D_subsetI:
  assumes "u \<rightarrow>\<^sup>* v"
  shows "D v \<subseteq> D u"
  using assms
  by (auto simp add: mem_D_iff_tree_path dest: tree_path_trans)

definition ND :: "'b \<Rightarrow> nat" where
  "ND v \<equiv> card (D v)"

definition non_empty_tree_path :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<rightarrow>\<^sup>+" 40) where
  "non_empty_tree_path u v \<equiv> (u, v) \<in> {(u, v). u \<rightarrow> v}\<^sup>+"

lemma non_empty_tree_pathE:
  assumes "u \<rightarrow>\<^sup>+ w"
  obtains v where
    "u \<rightarrow> v"
    "v \<rightarrow>\<^sup>* w"
  using assms
  unfolding non_empty_tree_path_def
proof (induct rule: trancl.induct)
  case r_into_trancl
  thus ?case
    using tree_path_refl
    by fast
next
  case trancl_into_trancl
  then show ?case
    by (auto simp add: tree_path_def intro: rtrancl_into_rtrancl)
qed

lemma non_empty_tree_pathE_2:
  assumes "u \<rightarrow>\<^sup>+ w"
  obtains v where
    "u \<rightarrow>\<^sup>*  v"
    "v \<rightarrow> w"
  using assms
  unfolding non_empty_tree_path_def
proof (induct rule: trancl.induct)
  case r_into_trancl
  thus ?case
    using tree_path_refl
    by fast
next
  case trancl_into_trancl
  then show ?case
    by (auto simp add: tree_path_def intro: rtrancl_into_rtrancl)
qed

lemma non_empty_tree_pathI:
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "v \<rightarrow> w"
  shows "u \<rightarrow>\<^sup>+ w"
  using assms
  by (auto simp add: tree_path_def non_empty_tree_path_def intro: rtrancl_into_trancl1)

lemma non_empty_tree_pathI_2:
  assumes "u \<rightarrow> v"
  assumes "v \<rightarrow>\<^sup>* w"
  shows "u \<rightarrow>\<^sup>+ w"
  using assms
  by (auto simp add: tree_path_def non_empty_tree_path_def intro: rtrancl_into_trancl2)

lemma non_empty_tree_path_if_tree_arc':
  assumes "u \<rightarrow> v"
  shows "u \<rightarrow>\<^sup>+ v"
  using assms
  by (auto simp add: non_empty_tree_path_def)

lemma
  assumes "u \<rightarrow>\<^sup>+ v"
  shows
    hd_non_empty_tree_path_mem_V: "u \<in> Directed_Multigraph.V (edges_from_map T)" and
    last_non_empty_tree_path_mem_V: "v \<in> Directed_Multigraph.V (edges_from_map T)"
  using assms
  unfolding non_empty_tree_path_def
  by (induct rule: trancl.induct) (auto dest: tail_tree_arc'_mem_V head_tree_arc'_mem_V)

lemma tree_path_non_empty_tree_path_cong:
  shows "u \<rightarrow>\<^sup>* v \<longleftrightarrow> u = v \<or> u \<rightarrow>\<^sup>+ v"
  using rtrancl_eq_or_trancl
  unfolding tree_path_def non_empty_tree_path_def
  by metis

lemma non_empty_tree_path_imp_tree_path:
  assumes "u \<rightarrow>\<^sup>+ v"
  shows "u \<rightarrow>\<^sup>* v"
  using assms
  by (simp add: tree_path_non_empty_tree_path_cong)

lemma non_empty_tree_path_imp_walk:
  assumes "u \<rightarrow>\<^sup>+ v"
  obtains p where
    "walk (edges_from_map T) p u v"
  using assms
  by (blast dest: non_empty_tree_path_imp_tree_path hd_non_empty_tree_path_mem_V elim: tree_path_imp_walk)

lemma non_empty_tree_path_imp_neq:
  assumes "u \<rightarrow>\<^sup>+ w"
  shows "w \<noteq> u"
proof (standard, goal_cases)
  case 1
  obtain v where
    v: "u \<rightarrow> v"
    "v \<rightarrow>\<^sup>* w"
    using assms
    by (elim non_empty_tree_pathE)
  then obtain p1 p2 where
    p1: "walk (edges_from_map T) p1 u v" and
    "walk (edges_from_map T) p2 v w"
    by (blast elim: tree_path_imp_walk dest: tree_path_if_tree_arc' tail_tree_arc'_mem_V head_tree_arc'_mem_V)
  hence "p1 = []"
    by (auto simp add: 1 dest: hd_vertex_mem_V walk_Nil unique_walk_3)
  hence "v = u"
    using p1
    by (simp add: walk_Nil_iff)
  thus ?case
    using v(1)
    by (auto dest: no_loop)
qed

lemma no_closed_tree_path:
  assumes "u \<rightarrow>\<^sup>+ v"
  shows "\<not> v \<rightarrow>\<^sup>* u"
proof (standard, goal_cases)
  obtain p1 where
    p1: "walk (edges_from_map T) p1 u v"
    using assms
    by (elim non_empty_tree_path_imp_walk)
  case 1
  hence "v \<rightarrow>\<^sup>+ u"
    using assms
    by (auto simp add: tree_path_non_empty_tree_path_cong)
  then obtain p2 where
    "walk (edges_from_map T) p2 v u"
    using assms
    by (elim non_empty_tree_path_imp_walk)
  hence "walk (edges_from_map T) (p1 @ p2) u u"
    using p1
    by (simp add: walk_append_iff last_vertex_eq)
  hence "rev_follow u = rev_follow u @ p1 @ p2"
    by (simp add: unique_walk_2)
  hence "v = u"
    using p1
    by (simp add: walk_Nil_iff)
  thus ?case
    using assms
    by (blast dest: non_empty_tree_path_imp_neq)
qed

lemma no_closed_tree_path_2:
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "u \<noteq> v"
  shows "\<not> v \<rightarrow>\<^sup>* u"
  using assms
  by (auto simp add: tree_path_non_empty_tree_path_cong dest: no_closed_tree_path)

lemma no_closed_tree_path_3:
  assumes "u \<rightarrow> v"
  shows "\<not> v \<rightarrow>\<^sup>* u"
  using assms
  by (blast dest: non_empty_tree_path_if_tree_arc' no_closed_tree_path)

lemma unique_tree_path:
  assumes "u \<rightarrow>\<^sup>+ x"
  assumes "v \<rightarrow>\<^sup>+ x"
  shows "u \<rightarrow>\<^sup>* v \<or> v \<rightarrow>\<^sup>* u"
proof -
  obtain p1 p2 where
    p1: "walk (edges_from_map T) p1 u x" and
    p2: "walk (edges_from_map T) p2 v x"
    using assms
    by (elim non_empty_tree_path_imp_walk)
  hence cong: "rev_follow v @ p2 = rev_follow u @ p1"
    by (simp add: unique_walk_2)
  let ?l1 = "length (rev_follow u)"
  let ?p3 = "drop ?l1 (rev_follow v)"
  let ?l2 = "length (rev_follow v)"
  let ?p4 = "drop ?l2 (rev_follow u)"
  show ?thesis
  proof (cases "?l2 \<le> ?l1")
    case True
    hence "p2 = ?p4 @ p1"
      using cong
      by (simp add: append_eq_append_conv_if)
    hence "walk (edges_from_map T) ?p4 v u"
      using p1 p2
      by (cases p1) (auto simp add: walk_Nil_iff walk_Cons_iff walk_append_iff)
    thus ?thesis
      by (blast dest: tree_path_if_walk)
  next
    case False
    hence "p1 = ?p3 @ p2"
      using cong
      by (simp add: append_eq_append_conv_if)
    hence "walk (edges_from_map T) ?p3 u v"
      using p1 p2
      by (cases p2) (auto simp add: walk_Nil_iff walk_Cons_iff walk_append_iff)
    thus ?thesis
      by (blast dest: tree_path_if_walk)
  qed
qed

lemma unique_tree_path_2:
  assumes "u \<rightarrow>\<^sup>* x"
  assumes "v \<rightarrow>\<^sup>* x"
  shows "u \<rightarrow>\<^sup>* v \<or> v \<rightarrow>\<^sup>* u"
proof (rule ccontr, goal_cases)
  case 1
  hence
    "u \<rightarrow>\<^sup>+ x"
    "v \<rightarrow>\<^sup>+ x"
    using assms
    by (auto simp add: tree_path_non_empty_tree_path_cong)
  thus ?case
    using 1
    by (fast dest: unique_tree_path)
qed

lemma unique_tree_path_3:
  assumes "u \<rightarrow> v"
  assumes "x \<rightarrow>\<^sup>* v"
  shows "x \<rightarrow>\<^sup>* u \<or> x = v"
proof (rule ccontr, goal_cases)
  case 1
  hence "x \<rightarrow>\<^sup>+ v"
    using assms(2)
    by (simp add: tree_path_non_empty_tree_path_cong)
  then obtain e p2 where
    e: "walk (edges_from_map T) [e] u v" and
    p2: "walk (edges_from_map T) p2 x v"
    using assms
    by
      (auto
        simp add: tree_arc'_iff_mem_endpoints walk_singleton_iff
        elim: non_empty_tree_path_imp_walk)
  hence cong: "rev_follow x @ p2 = rev_follow u @ [e]"
    by (simp add: unique_walk_2)
  let ?l1 = "length (rev_follow u)"
  let ?p3 = "drop ?l1 (rev_follow x)"
  let ?l2 = "length (rev_follow x)"
  let ?p4 = "drop ?l2 (rev_follow u)"
  show ?case
  proof (cases "?l2 \<le> ?l1")
    case True
    hence "p2 = ?p4 @ [e]"
      using cong
      by (simp add: append_eq_append_conv_if)
    hence "walk (edges_from_map T) ?p4 x u"
      using e p2
      by (simp add: walk_Cons_iff walk_snoc_iff)
    thus ?thesis
      using 1
      by (blast dest: tree_path_if_walk)
  next
    case False
    show ?thesis
    proof (cases p2)
      case Nil
      thus ?thesis
        using p2 1
        by (simp add: walk_Nil_iff)
    next
      case (Cons)
      thus ?thesis
        using cong False
        by (simp add: append_eq_append_conv_if append_eq_Cons_conv)
    qed
  qed
qed

lemma unique_tree_path_4:
  assumes "u \<rightarrow> x"
  assumes "v \<rightarrow> x"
  shows "v = u"
proof -
  have
    "v \<rightarrow>\<^sup>* u"
    "u \<rightarrow>\<^sup>* v"
    using assms
    by (blast dest: tree_path_if_tree_arc' unique_tree_path_3 no_loop)+
  thus ?thesis
    by (blast dest: no_closed_tree_path_2)
qed

lemma disjoint_siblings:
  assumes "v \<rightarrow> x"
  assumes "v \<rightarrow> y"
  assumes "y \<noteq> x"
  shows "D x \<inter> D y = {}"
proof -
  { fix z
    assume
      assm: "x \<rightarrow>\<^sup>* z"
      "y \<rightarrow>\<^sup>* z"
    then consider
      "x \<rightarrow>\<^sup>* y" |
      "y \<rightarrow>\<^sup>* x"
      by (blast dest: unique_tree_path_2)
    hence False
      using assms
      by (blast dest: unique_tree_path_3 no_closed_tree_path_3) }
  thus ?thesis
    by (fastforce simp add: mem_D_iff_tree_path)
qed

lemma D_eq_singleton_if:
  assumes "x \<notin> snd ` ran T"
  shows "D x = {x}"
proof -
  { fix v
    assume
      assm: "v \<in> D x"
      "v \<noteq> x"
    hence "x \<rightarrow>\<^sup>+ v"
      by (simp add: mem_D_iff_tree_path tree_path_non_empty_tree_path_cong)
    then obtain u where
      "x \<rightarrow> u"
      "u \<rightarrow>\<^sup>* v"
      by (elim non_empty_tree_pathE)
    hence False
      using assms
      by
        (force
          simp add: tree_arc'_def tree_arc_def tail_def Directed_Multigraph.endpoints_def
          intro: ranI) }
  thus ?thesis
    using D_refl
    by blast
qed

lemma D_subsetI_2:
  assumes "u \<rightarrow>\<^sup>+ v"
  shows "D v \<subset> D u"
proof -
  have "u \<notin> D v"
    using assms
    by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path)
  thus ?thesis
    using D_refl assms
    by (blast dest: non_empty_tree_path_imp_tree_path D_subsetI)
qed

lemma D_subset:
  assumes "v \<in> Directed_Multigraph.V (edges_from_map T)"
  shows "D v \<subseteq> Directed_Multigraph.V (edges_from_map T)"
  using assms
  by (auto simp add: mem_D_iff_tree_path tree_path_non_empty_tree_path_cong dest: last_non_empty_tree_path_mem_V)

(**)

(* TODO: Rename. *)
definition agublagu :: "'b \<Rightarrow> 'b \<rightharpoonup> 'a \<times> 'b" where
  "agublagu u v \<equiv> if u \<rightarrow>\<^sup>+ v then T v else None"

lemma agublagu_eq_NoneD:
  assumes "agublagu x v = None"
  shows "\<not> x \<rightarrow>\<^sup>+ v"
proof (standard, goal_cases)
  case 1
  then obtain u where
    "x \<rightarrow>\<^sup>* u"
    "u \<rightarrow> v"
    by (elim non_empty_tree_pathE_2)
  hence "T v \<noteq> None"
    by (auto simp add: tree_arc'_def tree_arc_def head_def Directed_Multigraph.endpoints_def)
  thus ?case
    using assms 1
    by (simp add: agublagu_def)
qed

lemma agublagu_eq_SomeD:
  assumes "agublagu x v = Some (\<epsilon>, u)"
  shows
    "u \<rightarrow> v"
    "x \<rightarrow>\<^sup>+ v"
  using assms
  by
    (auto
      simp add: agublagu_def tree_arc'_def tree_arc_def head_def tail_def Directed_Multigraph.endpoints_def
      split: if_splits)

lemma agublagu_eq_restrict_map:
  shows "agublagu u = T |` {v. u \<rightarrow>\<^sup>+ v}"
  by (auto simp add: agublagu_def restrict_map_def)

lemma map_le_agublagu:
  shows "agublagu u \<subseteq>\<^sub>m T"
  by (simp add: agublagu_eq_restrict_map map_le_def)

lemma edges_from_map_agublagu_subset:
  shows "edges_from_map (agublagu u) \<subseteq> edges_from_map T"
  using map_le_agublagu
  by (intro edges_from_map_subset_if_map_le)

lemma tree_agublagu:
  shows "tree (agublagu x) x"
proof (standard, goal_cases)
  case 1
  show ?case
    using wf
    by (auto simp add: agublagu_def intro: wf_subset)
next
  case 2
  show ?case
    by (auto simp add: agublagu_def dest: non_empty_tree_path_imp_neq)
next
  case (3 v)
  let ?T' = "agublagu x"
  have tbd: "tbd ?T'"
  proof (standard, goal_cases)
    case 1
    show ?case
      using wf
      by (auto simp add: agublagu_def intro: wf_subset)
  qed
  show ?case
    using 3
  proof (induct v rule: tbd.follow_induct[OF tbd])
    case (1 v)
    show ?case
    proof (cases rule: tbd.cases_m[OF tbd, of v])
      case 1
      thus ?thesis
        using "1.prems"
        by blast
    next
      case T'_v_eq_Some: (2 \<epsilon> u)
      show ?thesis
      proof (cases rule: tbd.cases_m[OF tbd, of u])
        case 1
        have "u = x"
        proof -
          have "x \<rightarrow>\<^sup>* u"
          proof -
            have
              "u \<rightarrow> v"
              "x \<rightarrow>\<^sup>+ v"
              using T'_v_eq_Some
              by (blast dest: agublagu_eq_SomeD)+
            thus ?thesis
              by (blast dest: non_empty_tree_path_imp_tree_path unique_tree_path_3 non_empty_tree_path_imp_neq)
          qed
          moreover have "\<not> x \<rightarrow>\<^sup>+ u"
            using 1
            by (blast dest: agublagu_eq_NoneD)
          ultimately show ?thesis
            by (simp add: tree_path_non_empty_tree_path_cong)
        qed
        thus ?thesis
          using tbd T'_v_eq_Some 1
          by (simp add: tbd.follow_simps tail_def Directed_Multigraph.endpoints_def)
      next
        case 2
        thus ?thesis
          using tbd T'_v_eq_Some
          by (auto simp add: tbd.follow_simps dest: "1.hyps")
      qed
    qed
  qed
qed

lemma agublagu_9:
  assumes "u \<in> Directed_Multigraph.V (edges_from_map (agublagu x))"
  shows "x \<rightarrow>\<^sup>* u"
proof -
  let ?T' = "agublagu x"
  obtain v where
    "(u, v) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T' \<or>
     (v, u) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T'"
    using assms
    by (elim Directed_Multigraph.mem_VE)
  then consider
    (u_v) "(u, v) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T'" |
    (v_u) "(v, u) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T'"
    by fast
  thus ?thesis
  proof (cases)
    case u_v
    then obtain \<epsilon> where
      "(\<epsilon>, u, v) \<in> edges_from_map ?T'"
      by (auto simp add: Directed_Multigraph.mem_endpoints_iff)
    hence
      "u \<rightarrow> v"
      "x \<rightarrow>\<^sup>+ v"
      by (blast dest: mem_edges_from_mapD_2 agublagu_eq_SomeD)+
    thus ?thesis
      by (blast dest: non_empty_tree_path_imp_tree_path unique_tree_path_3 non_empty_tree_path_imp_neq)
  next
    case v_u
    thus ?thesis
      by (auto simp add: Directed_Multigraph.mem_endpoints_iff dest: mem_edges_from_mapD_2 agublagu_eq_SomeD(2) non_empty_tree_path_imp_tree_path)
  qed  
qed

lemma agublagu_10:
  assumes "v \<in> snd ` ran T"
  shows "Directed_Multigraph.V (edges_from_map (agublagu v)) = D v"
proof (standard, goal_cases)
  case 1
  show ?case
    by (auto simp add: mem_D_iff_tree_path intro: agublagu_9)
next
  case 2
  let ?T' = "agublagu v"
  show ?case
  proof (standard, goal_cases)
    case (1 x)
    then consider
      (eq) "x = v" |
      (non_empty_tree_path) "v \<rightarrow>\<^sup>+ x"
      by (auto simp add: mem_D_iff_tree_path tree_path_non_empty_tree_path_cong)
    thus ?case
    proof (cases)
      case eq
      then obtain \<epsilon> y where
        "T y = Some (\<epsilon>, x)"
        "v \<rightarrow>\<^sup>+ y"
        using assms
        by (fastforce simp add: ran_def intro: tree_arc'I_2 non_empty_tree_path_if_tree_arc')
      thus ?thesis
        by (fastforce simp add: agublagu_def intro: mem_edges_from_mapI tail_mem_V_2)
    next
      case non_empty_tree_path
      hence "?T' x \<noteq> None"
        using agublagu_eq_NoneD
        by blast
      then obtain \<epsilon> y where
        "T x = Some (\<epsilon>, y)"
        by (auto simp add: agublagu_def split: if_splits)
      thus ?thesis
        using non_empty_tree_path
        by (fastforce simp add: agublagu_def intro: mem_edges_from_mapI head_mem_V_2)
    qed
  qed
qed

definition agublagu_3 :: "'b \<Rightarrow> 'b \<rightharpoonup> 'a \<times> 'b" where
  "agublagu_3 u v \<equiv> if u \<rightarrow>\<^sup>* v then None else T v"

lemma agublagu_3_eq_NoneD:
  assumes "agublagu_3 x v = None"
  shows "x \<rightarrow>\<^sup>* v \<or> T v = None"
  using assms
  by (simp add: agublagu_3_def split: if_splits)

lemma agublagu_3_eq_SomeD:
  assumes "agublagu_3 x v = Some (\<epsilon>, u)"
  shows
    "\<not> x \<rightarrow>\<^sup>* v"
    "T v = Some (\<epsilon>, u)"
  using assms
  by (simp_all add: agublagu_3_def split: if_splits)

lemma agublagu_3_eq_restrict_map:
  shows "agublagu_3 u = T |` (- D u)"
  by (auto simp add: agublagu_3_def mem_D_iff_tree_path)

lemma map_le_agublagu_3:
  shows "agublagu_3 u \<subseteq>\<^sub>m T"
  by (simp add: agublagu_3_eq_restrict_map map_le_def)

lemma edges_from_map_agublagu_3_subset:
  shows "edges_from_map (agublagu_3 u) \<subseteq> edges_from_map T"
  using map_le_agublagu_3
  by (intro edges_from_map_subset_if_map_le)

lemma tree_agublagu_3:
  shows "tree (agublagu_3 x) r"
proof (standard, goal_cases)
  case 1
  show ?case
    using wf
    by (auto simp add: agublagu_3_def intro: wf_subset)
next
  case 2
  show ?case
    using T_r_eq_None
    by (simp add: agublagu_3_def)
next
  let ?T' = "agublagu_3 x"
  case (3 v)
  have tbd: "tbd ?T'"
  proof (standard, goal_cases)
    case 1
    show ?case
      using wf
      by (auto simp add: agublagu_3_def intro: wf_subset)
  qed
  show ?case
    using 3
  proof (induct v rule: tbd.follow_induct[OF tbd])
    case (1 v)
    show ?case
    proof (cases rule: tbd.cases_m[OF tbd, of v])
      case 1
      thus ?thesis
        using "1.prems"
        by simp
    next
      case T'_v_eq_Some: (2 \<epsilon> u)
      show ?thesis
      proof (cases rule: tbd.cases_m[OF tbd, of u])
        case T'_u_eq_None: 1
        then consider
          "x \<rightarrow>\<^sup>* u" |
          "T u = None"
          by (force dest: agublagu_3_eq_NoneD)
        thus ?thesis
        proof (cases)
          case 1
          thus ?thesis
            using T'_v_eq_Some
            by (blast dest: agublagu_3_eq_SomeD tree_arc'I_2 tree_path_if_tree_arc' tree_path_trans)
        next
          case 2
          hence "u = r"
            using tail_last_follow_eq_r T'_v_eq_Some
            by
              (fastforce
                simp add: follow_simps tail_def Directed_Multigraph.endpoints_def
                dest: agublagu_3_eq_SomeD(2))
          thus ?thesis
            using tbd T'_v_eq_Some T'_u_eq_None
            by (simp add: tbd.follow_simps tail_def Directed_Multigraph.endpoints_def)
        qed
      next
        case 2
        thus ?thesis
          using tbd T'_v_eq_Some
          by (auto simp add: tbd.follow_simps dest: "1.hyps")
      qed
    qed
  qed
qed

lemma agublagu_3_9:
  assumes "u \<in> Directed_Multigraph.V (edges_from_map (agublagu_3 x))"
  shows "\<not> x \<rightarrow>\<^sup>* u"
proof -
  let ?T' = "agublagu_3 x"
  obtain v where
    "(u, v) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T' \<or>
     (v, u) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T'"
    using assms
    by (elim Directed_Multigraph.mem_VE)
  then consider
    (u_v) "(u, v) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T'" |
    (v_u) "(v, u) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T'"
    by fast
  thus ?thesis
  proof (cases)
    case u_v
    show ?thesis
    proof (standard, goal_cases)
      case 1
      obtain \<epsilon> where
        "(\<epsilon>, u, v) \<in> edges_from_map ?T'"
        using u_v
        by (auto simp add: Directed_Multigraph.mem_endpoints_iff)
      thus ?case
        using 1
        by (fast dest: mem_edges_from_mapD_2 agublagu_3_eq_SomeD tree_arc'I_2 tree_path_if_tree_arc' tree_path_trans)
    qed
  next
    case v_u
    thus ?thesis
      by (auto simp add: Directed_Multigraph.mem_endpoints_iff dest: mem_edges_from_mapD_2 agublagu_3_eq_SomeD(1))
  qed
qed

(* QQQ *)
\<comment> \<open>
This lemma is false! If v is the child of r, then agublagu_3 v is the empty map but D r - D v = {r}.
\<close>
lemma agublagu_3_10:
  assumes "r \<in> snd ` ran T"
  shows "Directed_Multigraph.V (edges_from_map (agublagu_3 v)) = D r - D v"
proof (standard, goal_cases)
  let ?T' = "agublagu_3 v"
  case 1
  show ?case
  proof (standard, goal_cases)
    case (1 x)
    have "r \<rightarrow>\<^sup>* x"
    proof -
      obtain y where
        "(x, y) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T' \<or>
         (y, x) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T'"
        using 1
        by (elim Directed_Multigraph.mem_VE)
      then consider
        (x_y) "(x, y) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T'" |
        (y_x) "(y, x) \<in> Directed_Multigraph.endpoints ` edges_from_map ?T'"
        by fast
      thus ?thesis
      proof (cases)
        case x_y
        then obtain \<epsilon> where
          T_y_eq_Some: "T y = Some (\<epsilon>, x)"
          by
            (auto
              simp add: Directed_Multigraph.mem_endpoints_iff
              dest: mem_edges_from_mapD_2 agublagu_3_eq_SomeD(2))
        hence
          "x \<rightarrow> y"
          "r \<rightarrow>\<^sup>* y"
          by (blast intro: tree_arc'I_2 walk_rev_follow tree_path_if_walk)+
        then show ?thesis
          using T_y_eq_Some T_r_eq_None
          by (fastforce dest: unique_tree_path_3)
      next
        case y_x
        then obtain \<epsilon> where
          "(\<epsilon>, y, x) \<in> edges_from_map ?T'"
          by (auto simp add: Directed_Multigraph.mem_endpoints_iff)
        thus ?thesis
          by
            (fastforce
              dest: mem_edges_from_mapD_2 agublagu_3_eq_SomeD(2)
              intro: walk_rev_follow tree_path_if_walk)
      qed
    qed
    thus ?case
      using 1
      by (auto simp add: mem_D_iff_tree_path dest: agublagu_3_9)
  qed
next
  case 2
  thm agublagu_3_eq_NoneD
  thm unique_tree_path_3
  then show ?case sorry
qed

end

locale lololol =
  tree
  where T = T +
    other
  where other = other
  for T :: "'b \<rightharpoonup> 'a \<times> 'b"
    and other :: "('a, 'b) Multigraph.edge \<Rightarrow> 'b \<Rightarrow> 'b"
begin

lemma connected':
  shows "connected' (undirect ` edges_from_map T) (Directed_Multigraph.V (edges_from_map T))"
  sorry

end

(* QUESTION: Define via the graph induced by T? *)
locale tree_of =
  tree
  where T = T +
    Directed_Multigraph.finite_multigraph
  where G = P
  for T :: "'b \<rightharpoonup> 'a \<times> 'b"
    and P :: "('a, 'b) Directed_Multigraph.multigraph" +
  assumes r_mem_V: "r \<in> Directed_Multigraph.V P"
  assumes tree_arc_imp_edge: "tree_arc e \<Longrightarrow> e \<in> P"
begin

lemma edges_from_map_subset:
  shows "edges_from_map T \<subseteq> P"
  by (auto simp add: tree_arc_iff_edge intro: tree_arc_imp_edge)

lemma finite_edges_from_map:
  shows "finite (edges_from_map T)"
proof -
  have "edges_from_map T \<subseteq> P"
    by (auto simp add: tree_arc_iff_edge intro: tree_arc_imp_edge)
  thus ?thesis
    using finite_edges
    by (rule finite_subset)
qed

lemma tree_arc'E_2:
  assumes "u \<rightarrow> v"
  obtains \<epsilon> where
    "(\<epsilon>, u, v) \<in> P"
  using assms
  by (auto dest: tree_arc_imp_edge elim: tree_arc'E)

lemma
  assumes "u \<rightarrow> v"
  shows
    tail_tree_arc'_mem_V: "u \<in> Directed_Multigraph.V P" and
    head_tree_arc'_mem_V: "v \<in> Directed_Multigraph.V P"
  using assms
  by (auto dest: tree_arc_imp_edge tail_mem_V_2 head_mem_V_2 elim: tree_arc'E)

lemma
  assumes "u \<rightarrow>\<^sup>+ v"
  shows
    hd_non_empty_tree_path_mem_V: "u \<in> Directed_Multigraph.V P" and
    last_non_empty_tree_path_mem_V: "v \<in> Directed_Multigraph.V P"
  using assms
  unfolding non_empty_tree_path_def
  by (induct rule: trancl.induct) (auto dest: tail_tree_arc'_mem_V head_tree_arc'_mem_V)

lemma V_edges_from_map_subset:
  shows "Directed_Multigraph.V (edges_from_map T) \<subseteq> Directed_Multigraph.V P"
proof (standard)
  fix u
  assume "u \<in> Directed_Multigraph.V (edges_from_map T)"
  then obtain v where
    "(u, v) \<in> Directed_Multigraph.endpoints ` (edges_from_map T) \<or>
     (v, u) \<in> Directed_Multigraph.endpoints ` (edges_from_map T)"
    by (elim Directed_Multigraph.mem_VE)
  thus "u \<in> Directed_Multigraph.V P"
    by
      (auto
        simp add: tree_arc'_iff_mem_endpoints[symmetric]
        dest: head_tree_arc'_mem_V tail_tree_arc'_mem_V)
qed

lemma finite_D:
  shows "finite (D u)"
proof (cases "u \<in> Directed_Multigraph.V (edges_from_map T)")
  case True
  thus ?thesis
    using finite_vertices
    by (metis D_subset V_edges_from_map_subset finite_subset)
next
  case False
  have "D u = {u}"
  proof (standard, goal_cases)
    case 1
    { fix v
      assume
        assm: "v \<in> D u"
        "v \<noteq> u"
      hence "u \<rightarrow>\<^sup>+ v"
        by (simp add: mem_D_iff_tree_path tree_path_non_empty_tree_path_cong)
      hence False
        using tree_axioms False
        by (fast dest: tree.hd_non_empty_tree_path_mem_V) }
    thus ?case
      by blast
  next
    case 2
    show ?case
      using D_refl
      by auto
  qed
  thus ?thesis
    by simp
qed

lemma ND_greater_0:
  shows "0 < ND v"
  using D_refl finite_D
  by (auto simp add: ND_def card_gt_0_iff)

definition frond :: "('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool" where
  "frond e \<equiv> e \<in> P \<and> \<not> tree_arc e"

lemma frond_iff_not_tree_arc:
  assumes "e \<in> P"
  shows "frond e \<longleftrightarrow> \<not> tree_arc e"
  using assms
  by (simp add: frond_def)

definition frond' :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<hookrightarrow>" 40) where
  "frond' u v \<equiv> \<exists>\<epsilon>. frond (\<epsilon>, u, v)"

lemma frond'E:
  assumes "u \<hookrightarrow> v"
  obtains \<epsilon> where
    "(\<epsilon>, u, v) \<in> P"
  using assms
  by (auto simp add: frond'_def frond_def)

lemma frond'I:
  assumes "frond e"
  shows "tail e \<hookrightarrow> head e"
proof -
  have "frond (fst e, tail e, head e)"
    using assms
    by (simp add: Directed_Multigraph.head_def Directed_Multigraph.tail_def Directed_Multigraph.endpoints_def)
  thus ?thesis
    by (auto simp add: frond'_def)
qed

lemma
  assumes "u \<hookrightarrow> v"
  shows
    tail_frond'_mem_V: "u \<in> Directed_Multigraph.V P" and
    head_frond'_mem_V: "v \<in> Directed_Multigraph.V P"
  using assms
  by (auto dest: tail_mem_V_2 head_mem_V_2 elim: frond'E)

lemma edge_imp:
  assumes "(\<epsilon>, u, v) \<in> P"
  shows "u \<rightarrow> v \<or> u \<hookrightarrow> v"
  using assms
  by (fastforce simp add: tree_arc'_def frond'_def dest: frond_iff_not_tree_arc)

lemma edge_iff:
  shows "(\<exists>\<epsilon>. (\<epsilon>, u, v) \<in> P) \<longleftrightarrow> u \<rightarrow> v \<or> u \<hookrightarrow> v"
  by (auto dest: edge_imp elim: tree_arc'E_2 frond'E)

lemma edge_iff_2:
  shows "(u, v) \<in> Directed_Multigraph.endpoints ` P \<longleftrightarrow> u \<rightarrow> v \<or> u \<hookrightarrow> v"
  unfolding Directed_Multigraph.mem_endpoints_iff
  using edge_iff
  .

definition tree_path_snoc_frond' :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<rightarrow>\<^sup>*\<hookrightarrow>" 40) where
  "tree_path_snoc_frond' u v \<equiv> \<exists>x. u \<rightarrow>\<^sup>* x \<and> x \<hookrightarrow> v"

lemma tree_path_snoc_frond'E:
  assumes "u \<rightarrow>\<^sup>*\<hookrightarrow> w"
  obtains v where
    "u \<rightarrow>\<^sup>* v"
    "v \<hookrightarrow> w"
  using assms
  by (auto simp add: tree_path_snoc_frond'_def)

lemma tree_path_snoc_frond'I:
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "v \<hookrightarrow> w"
  shows "u \<rightarrow>\<^sup>*\<hookrightarrow> w"
  using assms
  by (auto simp add: tree_path_snoc_frond'_def)

lemma tree_path_snoc_frond'I_2:
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "v \<rightarrow>\<^sup>*\<hookrightarrow> w"
  shows "u \<rightarrow>\<^sup>*\<hookrightarrow> w"
  using assms
  by (auto simp add: tree_path_snoc_frond'_def dest: tree_path_trans)

lemma tree_path_snoc_frond'_if_frond':
  assumes "u \<hookrightarrow> v"
  shows "u \<rightarrow>\<^sup>*\<hookrightarrow> v"
  using tree_path_refl assms
  by (auto simp add: tree_path_snoc_frond'_def)

lemma tree_path_snoc_frond'_10:
  assumes "u \<rightarrow>\<^sup>*\<hookrightarrow> v"
  shows "u \<hookrightarrow> v \<or> (\<exists>x. u \<rightarrow> x \<and> x \<rightarrow>\<^sup>*\<hookrightarrow> v)"
  using assms
  by (force simp add: tree_path_snoc_frond'_def tree_path_non_empty_tree_path_cong elim: non_empty_tree_pathE)

lemma
  assumes "u \<rightarrow>\<^sup>*\<hookrightarrow> v"
  shows
    hd_tree_path_snoc_frond'_mem_V: "u \<in> Directed_Multigraph.V P" and
    last_tree_path_snoc_frond'_mem_V: "v \<in> Directed_Multigraph.V P"
proof (goal_cases)
  case 1
  obtain x where
    "u \<rightarrow>\<^sup>* x"
    "x \<hookrightarrow> v"
    using assms
    by (elim tree_path_snoc_frond'E)
  then consider
    "u \<hookrightarrow> v" |
    "u \<rightarrow>\<^sup>+ x"
    by (auto simp add: tree_path_non_empty_tree_path_cong)
  thus ?case
  proof (cases)
    case 1
    thus ?thesis
      by (intro tail_frond'_mem_V)
  next
    case 2
    thus ?thesis
      by (intro hd_non_empty_tree_path_mem_V)
  qed
next
  case 2
  show ?case
    using assms
    by (blast dest: head_frond'_mem_V elim: tree_path_snoc_frond'E)
qed

end

definition restrict_fun :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b list" where
  "restrict_fun f A \<equiv> (\<lambda>x. if x \<in> A then f x else [])"

lemma restrict_fun_eq_override_on:
  shows "restrict_fun f A = override_on (\<lambda>_. []) f A"
  by (simp add: restrict_fun_def override_on_def)

locale tree_of_2 =
  tree
  where T = T +
    finite_multigraph_2
  where I = I
  for T :: "'b \<rightharpoonup> 'a \<times> 'b"
    and I :: "'b \<Rightarrow> ('a \<times> 'b) list" +
  assumes r_mem_V: "r \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes T_eq_Some_imp_mem_I: "T v = Some (\<epsilon>, u) \<Longrightarrow> (\<epsilon>, v) \<in> set (I u)"
begin
sublocale tree_of r T "edges_from_fun I"
proof (standard, goal_cases)
  case 1
  show ?case
    using r_mem_V
    .
next
  case (2 e)
  let ?\<epsilon> = "fst e"
  let ?u = "tail e"
  let ?v = "head e"
  have "T ?v = Some (?\<epsilon>, ?u)"
    using 2
    by (simp add: tree_arc_def)
  hence "(?\<epsilon>, ?v) \<in> set (I ?u)"
    by (intro T_eq_Some_imp_mem_I)
  hence "(?\<epsilon>, ?u, ?v) \<in> set (incidence I ?u)"
    by (force simp add: incidence_def to_edge_def)
  hence "e \<in> set (incidence I ?u)"
    by (simp add: Directed_Multigraph.tail_def Directed_Multigraph.head_def Directed_Multigraph.endpoints_def)
  thus ?case
    by (auto simp add: edges_from_fun_def)
qed

(* TODO: Move. *)
function (domintros) flatten :: "'b \<Rightarrow> ('a \<times> 'b) list" where
  "flatten u =
   fold
    (\<lambda>p. (@) (p # (if tree_arc (fst p, u, snd p) then flatten (snd p) else [])))
    (I u)
    []"
  by auto

(* TODO: Move. *)
definition agublagu_2 :: "'b \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list" where
  "agublagu_2 u v \<equiv> if u \<rightarrow>\<^sup>* v then I v else []"

lemma agublagu_2_eq_restrict_fun:
  shows "agublagu_2 u = restrict_fun I (D u)"
  by (auto simp add: agublagu_2_def restrict_fun_def D_def)

lemma flatten_pinduct:
  assumes "flatten_dom u"
  assumes "\<And>u. (\<And>p. p \<in> set (I u) \<Longrightarrow> tree_arc (fst p, u, snd p) \<Longrightarrow> P (snd p)) \<Longrightarrow> P u"
  shows "P u"
  using assms
  by (rule flatten.pinduct)

end

locale spanning_tree = tree_of +
  assumes spanning: "v \<in> Directed_Multigraph.V P \<Longrightarrow> v \<in> Directed_Multigraph.V (edges_from_map T)"
begin

lemma tree_path_if_mem_V:
  assumes "u \<in> Directed_Multigraph.V P"
  shows "r \<rightarrow>\<^sup>* u"
proof -
  obtain v where
      "(u, v) \<in> Directed_Multigraph.endpoints ` (edges_from_map T) \<or>
       (v, u) \<in> Directed_Multigraph.endpoints ` (edges_from_map T)"
    using assms
    by (fastforce elim: Directed_Multigraph.mem_VE dest: spanning)
  then consider
    (u_v) "(u, v) \<in> Directed_Multigraph.endpoints ` (edges_from_map T)" |
    (v_u) "(v, u) \<in> Directed_Multigraph.endpoints ` (edges_from_map T)"
    by blast
  thus ?thesis
  proof (cases)
    case u_v
    have T_v_neq_None: "T v \<noteq> None"
      using u_v
      by (auto simp add: head_def Directed_Multigraph.endpoints_def dest: mem_edges_from_mapD)
    show ?thesis
    proof (rule ccontr, goal_cases)
      case 1
      have "u \<rightarrow> v"
        using u_v
        by (simp add: tree_arc'_iff_mem_endpoints)
      moreover have "r \<rightarrow>\<^sup>* v"
        using T_v_neq_None
        by (auto intro: walk_rev_follow tree_path_if_walk)
      ultimately have "r = v"
        using 1
        by (blast dest: unique_tree_path_3)
      thus ?case
        using T_r_eq_None T_v_neq_None
        by blast
    qed
  next
    case v_u
    hence "T u \<noteq> None"
      using v_u
      by (auto simp add: head_def Directed_Multigraph.endpoints_def dest: mem_edges_from_mapD)
    thus ?thesis
      by (auto intro: walk_rev_follow tree_path_if_walk)
  qed
qed

lemma V_eq:
  shows "Directed_Multigraph.V P = Directed_Multigraph.V (edges_from_map T)"
  using V_edges_from_map_subset
  by (blast intro: spanning)

end

locale spanning_tree_2 = tree_of_2 +
  assumes spanning: "v \<in> Directed_Multigraph.V (edges_from_fun I) \<Longrightarrow> v \<in> Directed_Multigraph.V (edges_from_map T)"
begin
sublocale spanning_tree r T "edges_from_fun I"
proof (standard, goal_cases)
  case (1 v)
  thus ?case
    by (intro spanning)
qed
end

locale palm_tree = spanning_tree +
  assumes frond'_imp_tree_path: "u \<hookrightarrow> v \<Longrightarrow> v \<rightarrow>\<^sup>* u"
begin

lemma tree_path_snoc_frond'_imp_tree_path:
  assumes "u \<rightarrow>\<^sup>*\<hookrightarrow> v"
  shows "u \<rightarrow>\<^sup>* v \<or> v \<rightarrow>\<^sup>* u"
  using assms
  by (auto dest: frond'_imp_tree_path unique_tree_path_2 elim: tree_path_snoc_frond'E)

lemma D_r_eq_V:
  shows "D r = Directed_Multigraph.V P"
proof (standard, standard, goal_cases)
  case (1 v)
  thus ?case
    using r_mem_V
    by
      (auto
        simp add: mem_D_iff_tree_path tree_path_non_empty_tree_path_cong
        dest: last_non_empty_tree_path_mem_V)
next
  case 2
  show ?case
    by (auto simp add: mem_D_iff_tree_path intro: tree_path_if_mem_V)
qed
end

locale palm_tree_2 = spanning_tree_2 +
  assumes frond'_imp_tree_path: "frond' u v \<Longrightarrow> v \<rightarrow>\<^sup>* u"
begin
sublocale palm_tree r T "edges_from_fun I"
proof (standard, goal_cases)
  case (1 u v)
  thus ?case
    by (intro frond'_imp_tree_path)
qed
end

locale palm_tree_of =
  palm_tree
  where P = P +
    Multigraph.finite_multigraph
  where G = G
  for P :: "('a, 'b) Directed_Multigraph.multigraph"
    and G :: "('a, 'b) Multigraph.multigraph" +
  assumes undirect_P_eq_G: "undirect ` P = G"
begin
sublocale lololol r T other
  ..
sublocale huehuehue P other
  ..
end

lemma (in huehuehue) is_palm_tree_of_image_undirect:
  assumes "palm_tree r T G"
  shows "palm_tree_of r T other G (undirect ` G)"
  using assms finite_multigraph_axioms
  by (auto simp add: palm_tree_of_axioms_def intro: palm_tree_of.intro)

context palm_tree_of
begin

lemma connected'_D:
  assumes "v \<in> Directed_Multigraph.V P"
  shows "connected' (undirect ` P) (D v)"
proof (cases "v \<in> snd ` ran T")
  case True
  let ?T' = "agublagu v"
  have "lololol v ?T' other"
    using tree_agublagu other_axioms
    by (intro lololol.intro)
  hence "connected' (undirect ` edges_from_map ?T') (Directed_Multigraph.V (edges_from_map ?T'))"
    by (intro lololol.connected')
  hence "connected' (undirect ` edges_from_map T) (Directed_Multigraph.V (edges_from_map ?T'))"
    using edges_from_map_agublagu_subset
    by (blast dest: image_mono connected'_supergraph)
  hence "connected' (undirect ` P) (Directed_Multigraph.V (edges_from_map ?T'))"
    using edges_from_map_subset
    by (blast dest: image_mono connected'_supergraph)
  thus ?thesis
    using True
    by (simp add: V_eq agublagu_10)
next
  case False
  hence "D v = {v}"
    by (intro D_eq_singleton_if)
  thus ?thesis
    using assms
    by (auto simp add: V_image_undirect_eq intro: connected'_singleton)
qed

lemma tree_path_agublaguI:
  assumes "x \<rightarrow>\<^sup>* u"
  assumes "u \<rightarrow>\<^sup>* v"
  shows "tree.tree_path (agublagu x) u v"
  using assms(2)
  unfolding tree_path_def
  using assms(1)
proof (induct rule: rtrancl.induct)
  case (rtrancl_refl)
  show ?case
    using tree_agublagu
    by (fast dest: tree.tree_path_refl)
next
  case (rtrancl_into_rtrancl u v w)
  let ?T' = "agublagu x"
  have tree: "tree ?T' x"
    using tree_agublagu
    .
  have "tree.tree_arc' ?T' v w"
  proof -
    obtain \<epsilon>
      where "T w = Some (\<epsilon>, v)"
      using rtrancl_into_rtrancl.hyps(3)
      by
        (auto
          simp add: tree_arc_def head_def tail_def Directed_Multigraph.endpoints_def
          elim: tree_arc'E)
    moreover have "x \<rightarrow>\<^sup>+ w"
      using rtrancl_into_rtrancl.prems rtrancl_into_rtrancl.hyps(1, 3)
      by
        (auto
          simp add: tree_path_def non_empty_tree_path_def
          intro: rtrancl_into_trancl1 rtrancl_trancl_trancl)
    ultimately have "?T' w = Some (\<epsilon>, v)"
      by (simp add: agublagu_def)
    thus ?thesis
      using tree
      by (fastforce simp add: tree.tree_arc'_def tree.tree_arc_iff_edge intro: mem_edges_from_mapI)
  qed
  thus ?case
    using tree_agublagu rtrancl_into_rtrancl.hyps(2)[OF rtrancl_into_rtrancl.prems]
    by (fast intro: tree.tree_path_if_tree_arc' tree.tree_path_trans)
qed

lemma tree_path_agublaguD:
  assumes "tree.tree_path (agublagu x) u v"
  shows "u \<rightarrow>\<^sup>* v"
  using assms
  unfolding tree.tree_path_def[OF tree_agublagu]
proof (induct rule: rtrancl.induct)
  case (rtrancl_refl)
  show ?case
    using tree_path_refl
    .
next
  case (rtrancl_into_rtrancl u v w)
  let ?T' = "agublagu x"
  have tree: "tree ?T' x"
    using tree_agublagu
    .
  have "v \<rightarrow> w"
  proof -
    obtain \<epsilon>
      where "?T' w = Some (\<epsilon>, v)"
      using tree rtrancl_into_rtrancl.hyps(3)
      by
        (auto
          simp add: tree.tree_arc_def head_def tail_def Directed_Multigraph.endpoints_def
          intro: tree.tree_arc'E)
    hence "T w = Some (\<epsilon>, v)"
      by (simp add: agublagu_def split: if_splits)
    thus ?thesis
      by (auto simp add: tree_arc'_def tree_arc_iff_edge intro: mem_edges_from_mapI)
  qed
  thus ?case
    using rtrancl_into_rtrancl.hyps(2)
    by (fast intro: tree_path_if_tree_arc' tree_path_trans)
qed

lemma D_agublagu_eq:
  assumes "x \<rightarrow>\<^sup>* u"
  shows "tree.D (agublagu x) u = D u"
proof (standard, goal_cases)
  case 1
  let ?T' = "agublagu x"
  have tree: "tree ?T' x"
    using tree_agublagu
    .
  show ?case
  proof (standard, goal_cases)
    case (1 v)
    hence "tree.tree_path ?T' u v"
      using tree
      by (simp add: tree.mem_D_iff_tree_path)
    thus ?case
      by (auto simp add: mem_D_iff_tree_path dest: tree_path_agublaguD)
  qed
next
  case 2
  let ?T' = "agublagu x"
  have tree: "tree ?T' x"
    using tree_agublagu
    .
  show ?case
  proof (standard, goal_cases)
    case (1 v)
    hence "tree.tree_path ?T' u v"
      using assms
      by (auto simp add: mem_D_iff_tree_path intro: tree_path_agublaguI)
    thus ?case
      using tree
      by (simp add: tree.mem_D_iff_tree_path)
  qed
qed

lemma connected'_Diff_D:
  assumes "u \<in> Directed_Multigraph.V P"
  assumes "u \<rightarrow>\<^sup>* v"
  shows "connected' (undirect ` P) (D u - D v)"
proof (cases "u \<in> snd ` ran T")
  case True
  let ?T1 = "agublagu u"
  let ?T2 = "tree.agublagu_3 ?T1 v"
  have u_mem_ran_T1: "u \<in> snd ` ran ?T1"
  proof -
    obtain \<epsilon> x where
      "T x = Some (\<epsilon>, u)"
      using True
      by (auto simp add: ran_def)
    hence "?T1 x = Some (\<epsilon>, u)"
      by (auto simp add: agublagu_def dest: tree_arc'I_2 non_empty_tree_path_if_tree_arc')
    thus ?thesis
      by (force intro: ranI)
  qed
  have tree_T1: "tree ?T1 u"
    using tree_agublagu
    .
  hence "lololol u ?T2 other"
    using other_axioms
    by (fast intro: tree.tree_agublagu_3 lololol.intro)
  hence "connected' (undirect ` edges_from_map ?T2) (Directed_Multigraph.V (edges_from_map ?T2))"
    by (intro lololol.connected')
  hence "connected' (undirect ` edges_from_map ?T1) (Directed_Multigraph.V (edges_from_map ?T2))"
    using tree_T1
    by (blast dest: tree.edges_from_map_agublagu_3_subset image_mono connected'_supergraph)
  hence "connected' (undirect ` edges_from_map T) (Directed_Multigraph.V (edges_from_map ?T2))"
    using edges_from_map_agublagu_subset
    by (blast dest: image_mono connected'_supergraph)
  hence "connected' (undirect ` P) (Directed_Multigraph.V (edges_from_map ?T2))"
    using edges_from_map_subset
    by (blast dest: image_mono connected'_supergraph)
  hence "connected' (undirect ` P) (tree.D ?T1 u - tree.D ?T1 v)"
    using tree_T1 u_mem_ran_T1
    by (simp add: tree.agublagu_3_10)
  thus ?thesis
    using tree_path_refl assms(2)
    by (simp add: D_agublagu_eq)
next
  case False
  hence "D u = {u}"
    by (intro D_eq_singleton_if)
  thus ?thesis
    using connected'_empty assms(2)
    by (simp add: mem_D_iff_tree_path[symmetric])
qed

lemma D_subset_connected_component:
  assumes "v \<in> Directed_Multigraph.V P"
  shows "D v \<subseteq> connected_component (undirect ` P) v"
  sorry

lemma edge_iff_3:
  shows "{u, v} \<in> Multigraph.endpoints ` G \<longleftrightarrow> u \<rightarrow> v \<or> v \<rightarrow> u \<or> u \<hookrightarrow> v \<or> v \<hookrightarrow> u"
  by (auto simp add: undirect_P_eq_G[symmetric] mem_endpoints_image_undirect_iff edge_iff_2)

lemma cases_edge [consumes 1, case_names tree_arc_1 tree_arc_2 frond_1 frond_2]:
  assumes "{u, v} \<in> Multigraph.endpoints ` G"
  assumes "u \<rightarrow> v \<Longrightarrow> Q"
  assumes "v \<rightarrow> u \<Longrightarrow> Q"
  assumes "u \<hookrightarrow> v \<Longrightarrow> Q"
  assumes "v \<hookrightarrow> u \<Longrightarrow> Q"
  shows "Q"
  using assms
  by (auto simp add: edge_iff_3)

end

locale palm_tree_of_2 =
  palm_tree_2
  where I = I +
    Multigraph.finite_multigraph
  where G = G
  for I :: "'b \<Rightarrow> ('a \<times> 'b) list"
    and G :: "('a, 'b) Multigraph.multigraph" +
  assumes undirect_edges_from_fun_eq: "undirect ` edges_from_fun I = G"
begin
sublocale palm_tree_of r T other "edges_from_fun I" G
proof (standard, goal_cases)
  case 1
  show ?case
    using undirect_edges_from_fun_eq
    .
qed
end

end