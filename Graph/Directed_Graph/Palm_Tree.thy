theory Palm_Tree
  imports
    "../Undirected_Graph/Connectivity"
    Directed_Multigraph
    Tbd
begin

context tree
begin

definition tree_arc :: "('a, 'b) edge \<Rightarrow> bool" where
  "tree_arc e \<equiv> T (head e) = Some (fst e, tail e)"

definition tree_arc' :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<rightarrow>" 40) where
  "tree_arc' u v \<equiv> \<exists>\<epsilon>. tree_arc (\<epsilon>, u, v)"

lemma tree_arc'E:
  assumes "u \<rightarrow> v"
  obtains \<epsilon> where
    "tree_arc (\<epsilon>, u, v)"
  using assms
  by (auto simp add: tree_arc'_def)

lemma no_loop:
  assumes "u \<rightarrow> v"
  shows "v \<noteq> u"
  sorry

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

lemma no_closed_tree_path:
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "u \<noteq> v"
  shows "\<not> v \<rightarrow>\<^sup>* u"
  sorry

lemma no_closed_tree_path_2:
  assumes "u \<rightarrow> v"
  shows "\<not> v \<rightarrow>\<^sup>* u"
  using assms
  by (blast dest: tree_path_if_tree_arc' no_loop no_closed_tree_path)

lemma unique_tree_path:
  assumes "u \<rightarrow>\<^sup>* x"
  assumes "v \<rightarrow>\<^sup>* x"
  shows "u \<rightarrow>\<^sup>* v \<or> v \<rightarrow>\<^sup>* u"
  using assms
  sorry

lemma unique_tree_path_2:
  assumes "u \<rightarrow> v"
  assumes "x \<rightarrow>\<^sup>* v"
  shows "x \<rightarrow>\<^sup>* u \<or> x = v"
  sorry

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
      by (blast dest: unique_tree_path)
    hence False
    proof (cases)
      case 1
      hence "x \<rightarrow>\<^sup>* v"
        using assms(2, 3)
        by (blast dest: unique_tree_path_2)
      then show ?thesis sorry
    next
      case 2
      then show ?thesis sorry
    qed }
  thus ?thesis
    by (fastforce simp add: mem_D_iff_tree_path)
qed

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

lemma non_empty_tree_path_imp_neq:
  assumes "u \<rightarrow>\<^sup>+ v"
  shows "v \<noteq> u"
  using assms
  by (blast elim: non_empty_tree_pathE dest: no_closed_tree_path_2)

lemma no_closed_tree_path_3:
  assumes "u \<rightarrow>\<^sup>+ v"
  shows "\<not> v \<rightarrow>\<^sup>* u"
  using assms
  by (fastforce simp add: tree_path_non_empty_tree_path_cong dest: non_empty_tree_path_imp_neq no_closed_tree_path)

end

(* QUESTION: Define via the graph induced by T? *)
locale tree_of =
  tree
  where T = T +
    finite_multigraph
  where G = P
  for T :: "'b \<rightharpoonup> 'a \<times> 'b"
    and P :: "('a, 'b) multigraph" +
  assumes r_mem_V: "r \<in> V P"
  assumes tree_arc_imp_edge: "tree_arc e \<Longrightarrow> e \<in> P"
begin

lemma tree_arc'E_2:
  assumes "u \<rightarrow> v"
  obtains \<epsilon> where
    "(\<epsilon>, u, v) \<in> P"
  using assms
  by (auto dest: tree_arc_imp_edge elim: tree_arc'E)

lemma
  assumes "u \<rightarrow> v"
  shows
    tail_tree_arc'_mem_V: "u \<in> V P" and
    head_tree_arc'_mem_V: "v \<in> V P"
  using assms
  by (auto dest: tree_arc_imp_edge tail_mem_V_2 head_mem_V_2 elim: tree_arc'E)

lemma
  assumes "u \<rightarrow>\<^sup>+ v"
  shows
    hd_non_empty_tree_path_mem_V: "u \<in> V P" and
    last_non_empty_tree_path_mem_V: "v \<in> V P"
  using assms
  unfolding non_empty_tree_path_def
  by (induct rule: trancl.induct) (auto dest: tail_tree_arc'_mem_V head_tree_arc'_mem_V)

definition frond :: "('a, 'b) edge \<Rightarrow> bool" where
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

lemma
  assumes "u \<hookrightarrow> v"
  shows
    tail_frond'_mem_V: "u \<in> V P" and
    head_frond'_mem_V: "v \<in> V P"
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
  shows "(u, v) \<in> endpoints ` P \<longleftrightarrow> u \<rightarrow> v \<or> u \<hookrightarrow> v"
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

lemma
  assumes "u \<rightarrow>\<^sup>*\<hookrightarrow> v"
  shows
    hd_tree_path_snoc_frond'_mem_V: "u \<in> V P" and
    last_tree_path_snoc_frond'_mem_V: "v \<in> V P"
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

(* QUESTION: Define via the graph induced by T? *)
locale spanning_tree = tree_of +
  assumes spanning: "v \<in> V P \<Longrightarrow> r \<rightarrow>\<^sup>* v"

locale palm_tree = spanning_tree +
  assumes frond'_imp_tree_path: "u \<hookrightarrow> v \<Longrightarrow> v \<rightarrow>\<^sup>* u"
begin

lemma tree_path_snoc_frond'_imp_tree_path:
  assumes "u \<rightarrow>\<^sup>*\<hookrightarrow> v"
  shows "u \<rightarrow>\<^sup>* v \<or> v \<rightarrow>\<^sup>* u"
  using assms
  by (auto dest: frond'_imp_tree_path unique_tree_path elim: tree_path_snoc_frond'E)

(*
lemma tree_path_snoc_frond'_41:
  assumes "u \<rightarrow>\<^sup>* x"
  assumes "u \<rightarrow> v"
  assumes "v \<rightarrow>\<^sup>*\<hookrightarrow> x"
  shows "x = u \<or> v \<rightarrow>\<^sup>* x"
proof -
  consider
    "v \<rightarrow>\<^sup>* x" |
    "x \<rightarrow>\<^sup>* v"
    using assms(1, 4)
    by (auto dest: tree_path_snoc_frond'_40)
  thus ?thesis
  proof (cases)
    case 1
    thus ?thesis
      ..
  next
    case 2
    then show ?thesis
      using assms(1-3)
      by (auto dest: is_palm_treeD(1) tree_path_snoc_frond'_31)
  qed
qed
*)

lemma D_r_eq_V:
  shows "D r = V P"
  sorry

(*
lemma tree_path_snoc_frond'_1:
  assumes "b \<rightarrow> s"
  assumes "s \<rightarrow>\<^sup>* v"
  assumes "u \<rightarrow> v"
  shows "u \<in> D s \<union> {b}"
  sorry
*)

(*
lemma tree_path_snoc_frond'_2:
  assumes "s \<rightarrow>\<^sup>* b"
  assumes "u \<in> D s - D b"
  assumes "u \<rightarrow> v"
  shows "v \<in> D s - D b \<union> {b}"
  sorry
*)

(*
lemma tree_path_snoc_frond'_3:
  assumes "a \<rightarrow> s"
  assumes "s \<rightarrow>\<^sup>* b"
  assumes "v \<in> D s - D b"
  assumes "u \<rightarrow> v"
  shows "u \<in> D s - D b \<union> {a}"
  sorry
*)

end

fun undirect :: "('a, 'b) edge \<Rightarrow> ('a, 'b) Multigraph.edge" where
  "undirect (\<epsilon>, u, v) = (\<epsilon>, {u, v})"

lemma V_image_undirect_eq:
  shows "Multigraph.V (undirect ` G) = Directed_Multigraph.V G"
  sorry

lemma mem_image_undirect_iff:
  shows "(\<epsilon>, {u, v}) \<in> undirect ` G \<longleftrightarrow> (\<epsilon>, u, v) \<in> G \<or> (\<epsilon>, v, u) \<in> G"
  by (force simp add: doubleton_eq_iff)

lemma mem_endpoints_image_undirect_iff:
  shows
    "{u, v} \<in> Multigraph.endpoints ` undirect ` G \<longleftrightarrow>
     (u, v) \<in> Directed_Multigraph.endpoints ` G \<or> (v, u) \<in> Directed_Multigraph.endpoints ` G"
  unfolding Multigraph.mem_endpoints_iff Directed_Multigraph.mem_endpoints_iff mem_image_undirect_iff
  by blast

locale palm_tree_of =
  palm_tree
  where P = P +
    Multigraph.finite_multigraph
  where G = G
  for P :: "('a, 'b) multigraph"
    and G :: "('a, 'b) Multigraph.multigraph" +
  assumes undirect_P_eq_G: "undirect ` P = G"

lemma (in other) is_palm_tree_of_image_undirect:
  assumes "palm_tree r T P"
  shows "palm_tree_of r T other P (undirect ` P)"
  sorry

context palm_tree_of
begin

lemma connected'_D:
  assumes "v \<in> V P"
  shows "connected' (undirect ` P) (D v)"
  sorry

(* QUESTION: What is the generalization of this lemma? *)
lemma connected'_Diff_D:
  assumes "u \<in> V P"
  assumes "u \<notin> D v"
  shows "connected' (undirect ` P) (D u - D v)"
  sorry

lemma D_subset_connected_component:
  assumes "v \<in> V P"
  shows "D v \<subseteq> connected_component (undirect ` P) v"
  sorry

lemma edge_iff_3:
  shows "{u, v} \<in> Multigraph.endpoints ` G \<longleftrightarrow> u \<rightarrow> v \<or> v \<rightarrow> u \<or> u \<hookrightarrow> v \<or> v \<hookrightarrow> u"
  by (auto simp add: undirect_P_eq_G[symmetric] mem_endpoints_image_undirect_iff edge_iff_2)

(*
lemma is_palm_tree_of_1:
  assumes "(\<epsilon>, {u, v}) \<in> G"
  shows "u \<rightarrow> v \<or> v \<rightarrow> u \<or> u \<hookrightarrow> v \<or> v \<hookrightarrow> u"
  sorry
*)

(*
lemma is_palm_tree_of_2:
  assumes "u \<rightarrow> v \<or> v \<rightarrow> u \<or> u \<hookrightarrow> v \<or> v \<hookrightarrow> u"
  obtains \<epsilon> where
    "(\<epsilon>, {u, v}) \<in> G"
  using assms
  sorry
*)

(*
lemma is_palm_tree_of_10 [case_names 1 2 3 tree_arc_1 tree_arc_2 frond_1 frond_2]:
  assumes "e \<in> G"
  assumes "Multigraph.endpoints e = {u, v}"
  assumes "u \<rightarrow> v \<Longrightarrow> Q"
  assumes "v \<rightarrow> u \<Longrightarrow> Q"
  assumes "u \<hookrightarrow> v \<Longrightarrow> Q"
  assumes "v \<hookrightarrow> u \<Longrightarrow> Q"
  shows "Q"
  sorry
*)

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

end