section \<open>Hopcroft-Tarjan algorithm\<close>
theory Hopcroft_Tarjan
  imports
    "../Graph/Incidence_Structure/Directed_Incidence_Structure"
    "../Graph/Graph"
    "HOL-Data_Structures.Map_Specs"
    "../Graph/Incidence_Structure/Undirected_Incidence_Structure"
begin

subsection \<open>Finding separation pairs\<close>

definition is_numbering :: "'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
  "is_numbering S N \<equiv> bij_betw N S {1..card S}"

locale steps_1_2_3_high = palm_tree_2
  where T = T
  for T :: "'b \<rightharpoonup> ('a \<times> 'b)" +
  fixes N :: "'b \<Rightarrow> nat"
  assumes is_numbering: "is_numbering (Directed_Multigraph.V (edges_from_fun I)) N"
  assumes distinct_I: "distinct (I v)"

lemma (in steps_1_2_3_high) N_eq_iff:
  assumes "u \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "v \<in> Directed_Multigraph.V (edges_from_fun I)"
  shows "N u = N v \<longleftrightarrow> u = v"
  using is_numbering assms
  unfolding is_numbering_def
  by (metis bij_betw_iff_bijections)

lemma (in steps_1_2_3_high) N_geq_1:
  assumes "v \<in> Directed_Multigraph.V (edges_from_fun I)"
  shows "1 \<le> N v"
  using is_numbering assms
  by (auto simp add: is_numbering_def bij_betw_iff_bijections)

lemma (in steps_1_2_3_high) distinct_incidence:
  shows "distinct (incidence I v)"
  using distinct_I inj_to_edge
  by (fastforce simp add: incidence_def distinct_map to_edge_def dest: inj_on_if_inj)

definition (in steps_1_2_3_high) A :: "'b \<Rightarrow> 'b list" where
  "A v \<equiv> map snd (I v)"

lemma (in steps_1_2_3_high) A_incidence_cong:
  shows "A v = map head (incidence I v)"
  by (simp add: A_def head_def Directed_Multigraph.endpoints_def incidence_def to_edge_def)

lemma (in steps_1_2_3_high) mem_A_if_tree_arc':
  assumes "u \<rightarrow> v"
  shows "v \<in> set (A u)"
proof -
  obtain \<epsilon> where
    "tree_arc (\<epsilon>, u, v)"
    using assms
    by (elim tree_arc'E)
  hence "(\<epsilon>, u, v) \<in> edges_from_fun I"
    by (intro tree_arc_imp_edge)
  hence "(\<epsilon>, u, v) \<in> set (incidence I u)"
    using tail_eq
    by (fastforce simp add: edges_from_fun_def tail_def Directed_Multigraph.endpoints_def)
  thus ?thesis
    by (force simp add: A_incidence_cong head_def Directed_Multigraph.endpoints_def)
qed

(*
definition (in steps_1_2_3_high) children :: "'b \<Rightarrow> 'b list" where
  "children v \<equiv> filter (tree_arc' v) (A v)"
*)

definition (in steps_1_2_3_high) children :: "'b \<Rightarrow> 'b list" where
  "children v \<equiv> map head (filter tree_arc (incidence I v))"

lemma (in steps_1_2_3_high) mem_childrenD:
  assumes "v \<in> set (children u)"
  shows "u \<rightarrow> v"
proof -
  obtain e where
    "head e = v"
    "tree_arc e"
    "e \<in> set (incidence I u)"
    using assms
    by (auto simp add: children_def)
  thus ?thesis
    by (auto simp add: tail_eq dest: tree_arc'I)
qed

lemma (in steps_1_2_3_high) mem_childrenI:
  assumes "u \<rightarrow> v"
  shows "v \<in> set (children u)"
proof -
  obtain \<epsilon> where
    tree_arc: "tree_arc (\<epsilon>, u, v)"
    using assms
    by (elim tree_arc'E)
  hence "(\<epsilon>, u, v) \<in> edges_from_fun I"
    by (intro tree_arc_imp_edge)
  hence "(\<epsilon>, u, v) \<in> set (incidence I u)"
    using tail_eq
    by (fastforce simp add: edges_from_fun_def tail_def Directed_Multigraph.endpoints_def)
  thus ?thesis
    using tree_arc
    by (force simp add: children_def head_def Directed_Multigraph.endpoints_def)
qed

lemma (in steps_1_2_3_high) distinct_children:
  shows "distinct (children u)"
proof -
  { fix e e'
    assume
      "e \<in> set (filter tree_arc (incidence I u))"
      "e' \<in> set (filter tree_arc (incidence I u))"
      "head e' = head e"
    hence "e' = e"
      by (simp add: tree_arc_def head_def tail_def Directed_Multigraph.endpoints_def prod_eq_iff) }
  thus ?thesis
    using distinct_incidence
    by (simp add: children_def distinct_map inj_on_def)
qed

lemma (in steps_1_2_3_high) D_children_cong:
  shows "{u} \<union> \<Union> (D ` set (children u)) = D u"
proof -
  { fix v
    have "v = u \<or> v \<in> \<Union> (D ` set (children u)) \<longleftrightarrow> v = u \<or> (\<exists>x. u \<rightarrow> x \<and> x \<rightarrow>\<^sup>* v)"
      by (auto simp add: mem_D_iff_tree_path dest: mem_childrenD mem_childrenI)
    also have "... \<longleftrightarrow> v = u \<or> u \<rightarrow>\<^sup>+ v"
      by (blast elim: non_empty_tree_pathE intro: non_empty_tree_pathI_2)
    also have "... \<longleftrightarrow> u \<rightarrow>\<^sup>* v"
      by (auto simp add: tree_path_non_empty_tree_path_cong)
    also have "... \<longleftrightarrow> v \<in> D u"
      by (simp add: mem_D_iff_tree_path)
    finally have "v = u \<or> v \<in> \<Union> (D ` set (children u)) \<longleftrightarrow> v \<in> D u"
      . }
  thus ?thesis
    by blast
qed

lemma (in steps_1_2_3_high) ND_children_cong:
  shows "sum_list (map ND (children u)) + 1 = ND u"
proof -
  have "sum_list (map ND (children u)) + 1 = (\<Sum>v\<in>set (children u). card (D v)) + 1"
    using distinct_children
    by (simp add: sum_list_distinct_conv_sum_set ND_def)
  also have "... = card (\<Union> (D ` set (children u))) + 1"
    unfolding add_right_cancel
    using finite_set
  proof (rule card_UN_disjoint[symmetric], goal_cases)
    case 1
    show ?case
      using finite_D
      ..
  next
    case 2
    show ?case
      by (blast dest: mem_childrenD disjoint_siblings)
  qed
  also have "... = card {u} + card (\<Union> (D ` set (children u)))"
    by force
  also have "... = ND u"
    unfolding ND_def D_children_cong[of u, symmetric]
  proof (rule card_Un_disjoint[symmetric], goal_cases)
    case 2
    show ?case
      using finite_D
      by blast
  next
    case 3
    { fix v
      assume "v \<in> set (children u)"
      hence "u \<notin> D v"
        by (auto simp add: mem_D_iff_tree_path dest: mem_childrenD no_closed_tree_path_3) }
    thus ?case
      by fast
  qed simp
  finally show ?thesis
    .
qed

definition (in steps_1_2_3_high) agublagu_less :: "'b \<Rightarrow> nat \<Rightarrow> 'b list" where
  "agublagu_less v i \<equiv> take i (children v)"

definition (in steps_1_2_3_high) agublagu_geq :: "'b \<Rightarrow> nat \<Rightarrow> 'b list" where
  "agublagu_geq v i \<equiv> drop i (children v)"

lemma (in steps_1_2_3_high) children_agublagu_cong:
  shows "agublagu_less v i @ agublagu_geq v i = children v"
  unfolding agublagu_less_def agublagu_geq_def
  using append_take_drop_id
  .

lemma (in steps_1_2_3_high) mem_agublagu_less_imp_mem_children:
  assumes "v \<in> set (agublagu_less u i)"
  shows "v \<in> set (children u)"
  using assms
  by (auto simp add: agublagu_less_def dest: in_set_takeD)

lemma (in steps_1_2_3_high) mem_agublagu_geq_imp_mem_children:
  assumes "v \<in> set (agublagu_geq u i)"
  shows "v \<in> set (children u)"
  using assms
  by (auto simp add: agublagu_geq_def dest: in_set_dropD)

lemma (in steps_1_2_3_high) disjoint_agublagu_less_agublagu_geq:
  shows "set (agublagu_less u i) \<inter> set (agublagu_geq u i) = {}"
  using distinct_children
  by (metis children_agublagu_cong distinct_append)

definition (in steps_1_2_3_high) fukakyo_less :: "'b \<Rightarrow> nat \<Rightarrow> 'b set" where
  "fukakyo_less v i \<equiv> \<Union> (D ` set (agublagu_less v i))"

lemma (in steps_1_2_3_high) finite_fukakyo_less:
  shows "finite (fukakyo_less v i)"
  using finite_D
  by (simp add: fukakyo_less_def)

definition (in steps_1_2_3_high) fukakyo_geq :: "'b \<Rightarrow> nat \<Rightarrow> 'b set" where
  "fukakyo_geq v i \<equiv> \<Union> (D ` set (agublagu_geq v i))"

lemma (in steps_1_2_3_high) finite_fukakyo_geq:
  shows "finite (fukakyo_geq v i)"
  using finite_D
  by (simp add: fukakyo_geq_def)

lemma (in steps_1_2_3_high) D_fukakyo_cong:
  shows "{v} \<union> fukakyo_less v i \<union> fukakyo_geq v i = D v"
proof -
  have
    "{v} \<union> fukakyo_less v i \<union> fukakyo_geq v i =
     {v} \<union> \<Union> (D ` set (agublagu_less v i)) \<union> \<Union> (D ` set (agublagu_geq v i))"
    by (simp add: fukakyo_less_def fukakyo_geq_def)
  also have "... = {v} \<union> \<Union> (D ` (set (agublagu_less v i) \<union> set (agublagu_geq v i)))"
    by fast
  also have "... = {v} \<union> \<Union> (D ` (set (agublagu_less v i @ agublagu_geq v i)))"
    by auto
  also have "... = {v} \<union> \<Union> (D ` set (children v))"
    by (simp add: children_agublagu_cong)
  also have "... = D v"
    using D_children_cong
    .
  finally show ?thesis
    .
qed

lemma (in steps_1_2_3_high) idk_1:
  shows "{v} \<inter> fukakyo_less v i = {}"
  by
    (auto
      simp add: fukakyo_less_def mem_D_iff_tree_path
      dest: mem_agublagu_less_imp_mem_children mem_childrenD no_closed_tree_path_3)

lemma (in steps_1_2_3_high) idk_2:
  shows "{v} \<inter> fukakyo_geq v i = {}"
  by
    (auto
      simp add: fukakyo_geq_def mem_D_iff_tree_path
      dest: mem_agublagu_geq_imp_mem_children mem_childrenD no_closed_tree_path_3)

lemma (in steps_1_2_3_high) idk_3:
  shows "fukakyo_less u i \<inter> fukakyo_geq u i = {}"
proof -
  { fix x
    assume
      assm: "x \<in> fukakyo_less u i"
      "x \<in> fukakyo_geq u i"
    then obtain v v' where
      "v \<in> set (agublagu_less u i)"
      "x \<in> D v"
      "v' \<in> set (agublagu_geq u i)"
      "x \<in> D v'"
      by (auto simp add: fukakyo_less_def fukakyo_geq_def)
    hence
      "u \<rightarrow> v"
      "u \<rightarrow> v'"
      "v' \<noteq> v"
      "x \<in> D v"
      "x \<in> D v'"
      using disjoint_agublagu_less_agublagu_geq
      by (blast dest: mem_agublagu_less_imp_mem_children mem_agublagu_geq_imp_mem_children mem_childrenD)+
    hence False
      by (blast dest: disjoint_siblings) }
  thus ?thesis
    by blast
qed

lemma (in steps_1_2_3_high) idk_4:
  shows "card (fukakyo_less v i) + card (fukakyo_geq v i) + 1 = ND v"
proof -
  have "card (fukakyo_less v i) + card (fukakyo_geq v i) + 1 = card ({v} \<union> fukakyo_less v i \<union> fukakyo_geq v i)"
    using finite_fukakyo_less finite_fukakyo_geq idk_1 idk_2 idk_3
    by (simp add: card_Un_disjoint)
  also have "... = ND v"
    unfolding D_fukakyo_cong ND_def
    ..
  finally show ?thesis
    .
qed

lemma (in steps_1_2_3_high) idk_5:
  shows "sum_list (map ND (agublagu_less v i)) + sum_list (map ND (agublagu_geq v i)) + 1 = ND v"
  unfolding sum_list_append[symmetric] map_append[symmetric] children_agublagu_cong
  using ND_children_cong
  .

definition (in steps_1_2_3_high) lowpt1 :: "'b \<Rightarrow> 'b" where
  "lowpt1 u \<equiv> arg_min_on N ({u} \<union> {v. tree_path_snoc_frond' u v})"

definition (in steps_1_2_3_high) lowpt2 :: "'b \<Rightarrow> 'b" where
  "lowpt2 u \<equiv> arg_min_on N ({u} \<union> ({v. tree_path_snoc_frond' u v} - {lowpt1 u}))"

(*
TODO: This should follow from assumption palm_tree and probably be a lemma in theory Palm_Tree.
*)
lemma (in steps_1_2_3_high) finite_1:
  shows "finite {v. tree_path_snoc_frond' u v}"
  sorry

lemma (in steps_1_2_3_high) finite_2:
  shows "finite ({v. tree_path_snoc_frond' u v} - {lowpt1 u})"
  using finite_1
  by fast

lemma (in steps_1_2_3_high) lowpt1:
  shows "lowpt1 u = u \<or> tree_path_snoc_frond' u (lowpt1 u)"
proof -
  have "lowpt1 u \<in> {u} \<union> {v. tree_path_snoc_frond' u v}"
    unfolding lowpt1_def
    using finite_1
    by (intro arg_min_if_finite(1)) simp+
  thus ?thesis
    by blast
qed

lemma (in steps_1_2_3_high) lowpt1_mem_V:
  assumes "v \<in> Directed_Multigraph.V (edges_from_fun I)"
  shows "lowpt1 v \<in> Directed_Multigraph.V (edges_from_fun I)"
  using lowpt1 assms
  by (force dest: last_tree_path_snoc_frond'_mem_V)

lemma (in steps_1_2_3_high) N_lowpt1_least:
  assumes "tree_path_snoc_frond' u v"
  shows "N (lowpt1 u) \<le> N v"
  using finite_1 assms
  by (auto simp add: lowpt1_def intro: arg_min_least)

lemma (in steps_1_2_3_high) N_lowpt1_leq:
  shows "N (lowpt1 v) \<le> N v"
  using finite_1
  by (auto simp add: lowpt1_def intro: arg_min_least)

lemma (in steps_1_2_3_high) lowpt2:
  shows "lowpt2 u = u \<or> tree_path_snoc_frond' u (lowpt2 u)"
proof -
  have "lowpt2 u \<in> {u} \<union> ({v. tree_path_snoc_frond' u v} - {lowpt1 u})"
    unfolding lowpt2_def
    using finite_2
    by (intro arg_min_if_finite(1)) simp+
  thus ?thesis
    by blast
qed

lemma (in steps_1_2_3_high) lowpt2_eq_lowpt1_iff:
  shows "lowpt2 u = lowpt1 u \<longleftrightarrow> lowpt1 u = u"
  (* TODO: Beautify. *)
  by (metis Diff_iff Un_Diff_cancel Un_insert_left arg_min_if_finite(1) finite.insertI finite_2 insertCI insertE lowpt1_def lowpt2_def sup_bot_left)

lemma (in steps_1_2_3_high) N_lowpt2_leq:
  assumes "tree_path_snoc_frond' u v"
  assumes "lowpt1 u \<noteq> v"
  shows "N (lowpt2 u) \<le> N v"
  using assms
  (* TODO: Beautify. *)
  by (smt (verit, best) CollectI UnI2 arg_min_least finite.emptyI finite.insertI finite_UnI insertE insertI1 insert_Diff insert_Diff_single insert_commute insert_not_empty finite_2 lowpt2_def)

fun find_2_aux :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<times> 'a) list \<Rightarrow> 'b option" where
  "find_2_aux _ [] = None" |
  "find_2_aux P (p # ps) = (if P (snd p) then Some (fst p) else find_2_aux P ps)"

lemma find_2_aux_eq_None_iff:
  shows "find_2_aux P ps = None \<longleftrightarrow> \<not> (\<exists>p. p \<in> set ps \<and> P (snd p))"
proof (induct ps)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  thus ?case
    by (fastforce split: if_splits(2))
qed

lemma find_2_aux_eq_Some_iff:
  shows
    "find_2_aux P ps = Some a \<longleftrightarrow>
     (\<exists>i<length ps. P (snd (ps ! i)) \<and> a = fst (ps ! i) \<and> (\<forall>j<i. \<not> P (snd (ps ! j))))"
proof (induction ps)
  case Nil
  thus ?case
    by simp
next
  case (Cons p ps)
  thus ?case
  proof (cases "P (snd p)")
    case True
    thus ?thesis
      by force
  next
    case False 
    thus ?thesis
      (* TODO: Beautify. *)
      by (smt (verit) diff_Suc_1 find_2_aux.simps(2) length_Cons less_Suc_eq_0_disj list.sel(3) local.Cons nat.simps(3) nth_Cons' nth_tl)
  qed
qed

definition find_2 :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "find_2 P l \<equiv> find_2_aux P (enumerate 0 l)"

lemma find_2_eq_None_iff:
  shows "find_2 P l = None \<longleftrightarrow> \<not> (\<exists>x. x \<in> set l \<and> P x)"
  unfolding find_2_def enumerate_eq_zip
  using find_2_aux_eq_None_iff
  (* TODO: Beautify. *)
  by (metis add_diff_cancel_left' in_set_impl_in_set_zip2 length_upt prod.collapse set_zip_rightD snd_conv)

lemma find_2_eq_Some_iff:
  shows "find_2 P l = Some i \<longleftrightarrow> (i<length l \<and> P (l ! i) \<and> (\<forall>j<i. \<not> P (l ! j)))"
  unfolding find_2_def enumerate_eq_zip
  using find_2_aux_eq_Some_iff
  (* TODO: Beautify. *)
  by (smt (verit, ccfv_threshold) Nat.add_0_right Pair_inject add.commute add.left_commute add.right_neutral add_cancel_left_left add_lessD1 add_pos_pos enumerate_eq_zip gen_length_def length_code length_enumerate less_add_eq_less less_imp_add_positive nth_enumerate_eq prod.collapse verit_sum_simplify)

definition (in steps_1_2_3_high) i\<^sub>0 :: "'b \<Rightarrow> 'b \<Rightarrow> nat" where
  "i\<^sub>0 a b \<equiv>
   (case find_2 (\<lambda>v. N a \<le> N (lowpt1 v)) (children b) of None \<Rightarrow> length (children b) | Some i \<Rightarrow> i)"

lemma (in steps_1_2_3_high) i\<^sub>0_leq_length_children:
  shows "i\<^sub>0 a b \<le> length (children b)"
  by (auto simp add: i\<^sub>0_def find_2_eq_Some_iff split: option.split)

lemma (in steps_1_2_3_high) idk_69:
  shows "\<forall>i<i\<^sub>0 a b. N (lowpt1 (children b ! i)) < N a"
proof (cases "find_2 (\<lambda>v. N a \<le> N (lowpt1 v)) (children b)")
  case None
  hence "\<not> (\<exists>v. v \<in> set (children b) \<and> N a \<le> N (lowpt1 v))"
    unfolding find_2_eq_None_iff
    .
  thus ?thesis
    by (auto simp add: i\<^sub>0_def None intro: nth_mem)
next
  case (Some i)
  hence "\<forall>j<i. N (lowpt1 (children b ! j)) < N a"
    by (auto simp add: find_2_eq_Some_iff)
  thus ?thesis
    by (simp add: i\<^sub>0_def Some)
qed

lemma (in steps_1_2_3_high) idk_70:
  assumes "sorted_wrt (\<lambda>u v. N (lowpt1 u) \<le> N (lowpt1 v)) (children b)"
  assumes "i\<^sub>0 a b \<le> i"
  assumes "i < length (children b)"
  shows "N a \<le> N (lowpt1 (children b ! i))"
proof (cases "find_2 (\<lambda>v. N a \<le> N (lowpt1 v)) (children b)")
  case None
  hence "\<not> (\<exists>v. v \<in> set (children b) \<and> N a \<le> N (lowpt1 v))"
    unfolding find_2_eq_None_iff
    .
  thus ?thesis
    using assms(2-3)
    by (auto simp add: i\<^sub>0_def None)
next
  case Some
  hence "N a \<le> N (lowpt1 (children b ! i\<^sub>0 a b))"
    unfolding find_2_eq_Some_iff
    by (simp add: i\<^sub>0_def Some)
  also have "... \<le> N (lowpt1 (children b ! i))"
    using assms
    by (cases "i\<^sub>0 a b = i") (auto intro: sorted_wrt_nth_less)
  finally show ?thesis
    .
qed

lemma (in steps_1_2_3_high) mem_agublagu_lessD:
  assumes "b' \<in> set (agublagu_less b (i\<^sub>0 a b))"
  shows "N (lowpt1 b') < N a"
proof -
  obtain i where
    "i < i\<^sub>0 a b"
    "agublagu_less b (i\<^sub>0 a b) ! i = b'"
    using assms
    by (auto simp add: agublagu_less_def in_set_conv_nth)
  hence
    "i < i\<^sub>0 a b"
    "children b ! i = b'"
    by (simp_all add: agublagu_less_def)
  thus ?thesis
    using idk_69
    by fastforce
qed

lemma (in steps_1_2_3_high) mem_agublagu_lessI:
  assumes "sorted_wrt (\<lambda>u v. N (lowpt1 u) \<le> N (lowpt1 v)) (children b)"
  assumes "b \<rightarrow> b'"
  assumes "N (lowpt1 b') < N a"
  shows "b' \<in> set (agublagu_less b (i\<^sub>0 a b))"
proof -
  obtain i where
    i: "i < length (children b)"
    "children b ! i = b'"
    using assms(2)
    by (fastforce simp add: in_set_conv_nth dest: mem_childrenI)
  hence "i < i\<^sub>0 a b"
    using assms(1, 3)
    by (auto simp add: linorder_not_less dest: idk_70)
  hence
    "i < length (agublagu_less b (i\<^sub>0 a b))"
    "agublagu_less b (i\<^sub>0 a b) ! i = b'"
    using i
    by (simp_all add: agublagu_less_def)
  thus ?thesis
    by fastforce
qed

lemma (in steps_1_2_3_high) mem_agublagu_geqD:
  assumes "sorted_wrt (\<lambda>u v. N (lowpt1 u) \<le> N (lowpt1 v)) (children b)"
  assumes "b' \<in> set (agublagu_geq b (i\<^sub>0 a b))"
  shows "N a \<le> N (lowpt1 b')"
proof -
  obtain i where
    "i < length (agublagu_geq b (i\<^sub>0 a b))"
    "agublagu_geq b (i\<^sub>0 a b) ! i = b'"
    using assms(2)
    by (auto simp add: in_set_conv_nth)
  hence
    "i\<^sub>0 a b \<le> i\<^sub>0 a b + i"
    "i\<^sub>0 a b + i < length (children b)"
    "children b ! (i\<^sub>0 a b + i) = b'"
    by (fastforce simp add: agublagu_geq_def)+
  thus ?thesis
    using assms(1)
    by (blast intro: idk_70)
qed

lemma (in steps_1_2_3_high) mem_agublagu_geqI:
  assumes "b \<rightarrow> b'"
  assumes "N a \<le> N (lowpt1 b')"
  shows "b' \<in> set (agublagu_geq b (i\<^sub>0 a b))"
proof -
  obtain i where
    i: "i < length (children b)"
    "children b ! i = b'"
    using assms(1)
    by (fastforce simp add: in_set_conv_nth dest: mem_childrenI)
  hence "i\<^sub>0 a b \<le> i"
    using assms(2) idk_69
    by (fastforce simp add: linorder_not_less)
  hence
    "i - i\<^sub>0 a b < length (agublagu_geq b (i\<^sub>0 a b))"
    "agublagu_geq b (i\<^sub>0 a b) ! (i - i\<^sub>0 a b) = b'"
    using i
    by (simp_all add: agublagu_geq_def)
  thus ?thesis
    by force
qed

lemma (in steps_1_2_3_high) mem_fukakyo_lessE:
  assumes "v \<in> fukakyo_less b (i\<^sub>0 a b)"
  obtains b' where
    "b \<rightarrow> b'"
    "b' \<rightarrow>\<^sup>* v"
    "N (lowpt1 b') < N a"
proof -
  obtain b' where
    "b' \<in> set (agublagu_less b (i\<^sub>0 a b))"
    "v \<in> D b'"
    using assms
    by (auto simp add: fukakyo_less_def)
  thus ?thesis
    by
      (fastforce
        simp add: agublagu_less_def mem_D_iff_tree_path
        dest: in_set_takeD mem_childrenD mem_agublagu_lessD
        intro: that)
qed

lemma (in steps_1_2_3_high) mem_fukakyo_lessI:
  assumes "sorted_wrt (\<lambda>u v. N (lowpt1 u) \<le> N (lowpt1 v)) (children b)"
  assumes "b \<rightarrow> b'"
  assumes "b' \<rightarrow>\<^sup>* v"
  assumes "N (lowpt1 b') < N a"
  shows "v \<in> fukakyo_less b (i\<^sub>0 a b)"
  using assms
  by (auto simp add: fukakyo_less_def mem_D_iff_tree_path intro: mem_agublagu_lessI)

lemma (in steps_1_2_3_high) mem_fukakyo_geqE:
  assumes "sorted_wrt (\<lambda>u v. N (lowpt1 u) \<le> N (lowpt1 v)) (children b)"
  assumes "v \<in> fukakyo_geq b (i\<^sub>0 a b)"
  obtains b' where
    "b \<rightarrow> b'"
    "b' \<rightarrow>\<^sup>* v"
    "N a \<le> N (lowpt1 b')"
proof -
obtain b' where
    "b' \<in> set (agublagu_geq b (i\<^sub>0 a b))"
    "v \<in> D b'"
    using assms(2)
    by (auto simp add: fukakyo_geq_def)
  thus ?thesis
    using assms(1)
    by
      (fastforce
        simp add: agublagu_geq_def mem_D_iff_tree_path
        dest: in_set_dropD mem_childrenD mem_agublagu_geqD
        intro: that)
qed

lemma (in steps_1_2_3_high) mem_fukakyo_geqI:
  assumes "b \<rightarrow> b'"
  assumes "b' \<rightarrow>\<^sup>* v"
  assumes "N a \<le> N (lowpt1 b')"
  shows "v \<in> fukakyo_geq b (i\<^sub>0 a b)"
  using assms
  by (auto simp add: fukakyo_geq_def mem_D_iff_tree_path intro: mem_agublagu_geqI)

definition (in steps_1_2_3_high) \<phi> :: "'b \<Rightarrow> 'b \<Rightarrow> nat" where
  "\<phi> u v \<equiv>
   if u \<rightarrow> v then if N (lowpt2 v) < N u then 3 * N (lowpt1 v)
                     else 3 * N (lowpt1 v) + 2
   else 3 * N v + 1"

lemma (in steps_1_2_3_high) sorted_wrt_\<phi>_A:
  assumes "sorted_wrt (\<lambda>e e'. \<phi> (tail e) (head e) \<le> \<phi> (tail e') (head e')) (incidence I v)"
  shows "sorted_wrt (\<lambda>x y. \<phi> v x \<le> \<phi> v y) (A v)"
  using assms
  by
    (auto
      simp add: A_incidence_cong sorted_wrt_map tail_eq
      intro: sorted_wrt_mono_rel[where ?P = "\<lambda>e e'. \<phi> (tail e) (head e) \<le> \<phi> (tail e') (head e')"])

lemma (in steps_1_2_3_high) sorted_wrt_lowpt1_children:
  assumes "sorted_wrt (\<lambda>e e'. \<phi> (tail e) (head e) \<le> \<phi> (tail e') (head e')) (incidence I v)"
  shows "sorted_wrt (\<lambda>u v. N (lowpt1 u) \<le> N (lowpt1 v)) (children v)"
  unfolding children_def
  thm sorted_wrt_mono_rel
proof (rule sorted_wrt_mono_rel[where ?P = "\<lambda>x y. \<phi> v x \<le> \<phi> v y"], goal_cases)
  case (1 x y)
  consider
    "N (lowpt2 x) < N v \<and> N (lowpt2 y) < N v" |
    "N (lowpt2 x) < N v \<and> N v \<le> N (lowpt2 y)" |
    "N v \<le> N (lowpt2 x) \<and> N (lowpt2 y) < N v" |
    "N v \<le> N (lowpt2 x) \<and> N v \<le> N (lowpt2 y)"
    by linarith
  thus ?case
    using 1
    by (cases) (fastforce simp add: children_def[symmetric] \<phi>_def dest: mem_childrenD)+
next
  case 2
  show ?case
    unfolding sorted_wrt_map
  proof (rule sorted_wrt_mono_rel[where ?P = "\<lambda>e e'. \<phi> (tail e) (head e) \<le> \<phi> (tail e') (head e')"], goal_cases)
    case (1 e e')
    thus ?case
      by (auto simp add: tail_eq)
  next
    case 2
    show ?case
      using assms
      by (intro sorted_wrt_filter)
  qed
qed

locale steps_1_2_3_high_2 = steps_1_2_3_high +
  assumes P1: "N r = 1"
  assumes
    P2: "v \<in> Directed_Multigraph.V (edges_from_fun I) \<Longrightarrow>
         N (children v ! i) = N v + sum_list (map ND (agublagu_geq v (i + 1))) + 1"
    (* assumes P2: "v \<in> Directed_Multigraph.V (edges_from_fun I) \<Longrightarrow> N (children v ! i) = N v + card (fukakyo_geq v (i + 1)) + 1" *)
    (* QUESTION: Is this going to cause issues with Sorted_Less.sorted (incidence v G)? *)
  assumes P3: "sorted_wrt (\<lambda>e e'. \<phi> (tail e) (head e) \<le> \<phi> (tail e') (head e')) (incidence I v)"

locale steps_1_2_3_high_3 =
  biconnected_multigraph
  where G = G +
    steps_1_2_3_high_2
  where T = T
  for G :: "('a, 'b) Multigraph.multigraph"
    and T :: "'b \<rightharpoonup> 'a \<times> 'b" +
  assumes undirect_edges_from_fun_eq: "undirect ` edges_from_fun I = G"
begin
sublocale palm_tree_of_2 r T other I G
proof (standard, goal_cases)
  case 1
  show ?case
    using undirect_edges_from_fun_eq
    .
qed
end

lemma (in steps_1_2_3_high_3) V_E_I_eq_V_G:
  shows "Directed_Multigraph.V (edges_from_fun I) = Multigraph.V G"
  using V_image_undirect_eq[symmetric]
  unfolding undirect_P_eq_G[symmetric]
  .

lemma (in steps_1_2_3_high_2) N_less_if_tree_arc':
  assumes "u \<rightarrow> v"
  shows "N u < N v"
proof -
  obtain i where
    "i < length (children u)"
    "(children u) ! i = v"
    using assms
    by (fastforce simp add: in_set_conv_nth dest: mem_childrenI)
  thus ?thesis
    using assms
    by (auto simp add: P2 dest: tail_tree_arc'_mem_V)
qed

lemma (in steps_1_2_3_high_2) N_less_if_non_empty_tree_path:
  assumes "u \<rightarrow>\<^sup>+ v"
  shows "N u < N v"
  using assms
  unfolding non_empty_tree_path_def
  by (induct rule: trancl.induct) (auto dest: N_less_if_tree_arc')

lemma (in steps_1_2_3_high_2) N_leq_if_tree_path:
  assumes "u \<rightarrow>\<^sup>* v"
  shows "N u \<le> N v"
  using assms
  by (auto simp add: tree_path_non_empty_tree_path_cong dest: N_less_if_non_empty_tree_path)

(* TODO: Beautify. *)
lemma (in steps_1_2_3_high_2) N_lowpt1_tree_arc':
  assumes "u \<rightarrow> v"
  shows "N (lowpt1 u) \<le> N (lowpt1 v)"
  using assms
  by (metis N_less_if_tree_arc' N_lowpt1_least N_lowpt1_leq lowpt1 order.strict_implies_order order.strict_trans1 tree_path_if_tree_arc' tree_path_snoc_frond'I_2)

lemma (in steps_1_2_3_high_2) N_lowpt1_frond':
  assumes "frond' u v"
  shows "N (lowpt1 u) \<le> N v"
  using assms
  by (force dest: tree_path_snoc_frond'_if_frond' N_lowpt1_least)

lemma (in steps_1_2_3_high) mem_fukakyo_geq_1:
  assumes "sorted_wrt (\<lambda>u v. N (lowpt1 u) \<le> N (lowpt1 v)) (children b)"
  assumes "b \<rightarrow> b'"
  assumes "b' \<rightarrow>\<^sup>* v"
  shows "v \<in> fukakyo_geq b (i\<^sub>0 a b) \<longleftrightarrow> N a \<le> N (lowpt1 b')"
proof (standard, goal_cases)
  case 1
  then obtain b'' where
    b'': "b \<rightarrow> b''"
    "b'' \<rightarrow>\<^sup>* v"
    "N a \<le> N (lowpt1 b'')"
    using assms(1)
    by (elim mem_fukakyo_geqE)
  hence "b'' = b'"
    using assms(2, 3)
    by (fastforce simp add: mem_D_iff_tree_path dest: disjoint_siblings)
  thus ?case
    using b''(3)
    by simp
next
  case 2
  thus ?case
    using assms(2, 3)
    by (intro mem_fukakyo_geqI)
qed

definition (in steps_1_2_3_high) is_type_1_pair where
  "is_type_1_pair a b s t \<equiv>
   b \<noteq> a \<and>
   s \<noteq> a \<and>
   b \<rightarrow> s \<and>
   lowpt1 s = a \<and>
   N b \<le> N (lowpt2 s) \<and>
   t \<in> Directed_Multigraph.V (edges_from_fun I) \<and>
   t \<noteq> a \<and>
   t \<noteq> b \<and>
   t \<notin> D s"

lemma (in steps_1_2_3_high_2) is_type_1_pairD:
  assumes "is_type_1_pair a b s t"
  shows
    "a \<in> Directed_Multigraph.V (edges_from_fun I)"
    "b \<in> Directed_Multigraph.V (edges_from_fun I)"
    "b \<noteq> a"
    "s \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<noteq> a"
    "s \<noteq> b"
    "b \<rightarrow> s"
    "lowpt1 s = a"
    "N b \<le> N (lowpt2 s)"
    "t \<in> Directed_Multigraph.V (edges_from_fun I)"
    "t \<noteq> a"
    "t \<noteq> b"
    "t \<notin> D s"
proof -
  show
    "b \<noteq> a"
    "s \<noteq> a"
    "b \<rightarrow> s"
    "lowpt1 s = a"
    "N b \<le> N (lowpt2 s)"
    "t \<in> Directed_Multigraph.V (edges_from_fun I)"
    "t \<noteq> a"
    "t \<noteq> b"
    "t \<notin> D s"
    using assms
    by (simp_all add: is_type_1_pair_def)
  thus
    "a \<in> Directed_Multigraph.V (edges_from_fun I)"
    "b \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<noteq> b"
    by (auto dest: N_less_if_tree_arc' intro: lowpt1_mem_V tail_tree_arc'_mem_V head_tree_arc'_mem_V)
qed

lemma (in steps_1_2_3_high) is_type_1_pairI:
  assumes
    "b \<noteq> a"
    "s \<noteq> a"
    "b \<rightarrow> s"
    "lowpt1 s = a"
    "N b \<le> N (lowpt2 s)"
    "t \<in> Directed_Multigraph.V (edges_from_fun I)"
    "t \<noteq> a"
    "t \<noteq> b"
    "t \<notin> D s"
  shows "is_type_1_pair a b s t"
  using assms
  by (simp add: is_type_1_pair_def)

definition (in steps_1_2_3_high) is_type_1_pair' where
  "is_type_1_pair' a b \<equiv> \<exists>s t. is_type_1_pair a b s t"

lemma (in steps_1_2_3_high_2) is_type_1_pair'D:
  assumes "is_type_1_pair' a b"
  shows
    "a \<in> Directed_Multigraph.V (edges_from_fun I)"
    "b \<in> Directed_Multigraph.V (edges_from_fun I)"
    "b \<noteq> a"
  using assms
  by (auto simp add: is_type_1_pair'_def dest: is_type_1_pairD(1-3))

lemma (in steps_1_2_3_high_2) is_type_1_pair'E:
  assumes "is_type_1_pair' a b"
  obtains s t where
    "s \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<noteq> a"
    "s \<noteq> b"
    "b \<rightarrow> s"
    "lowpt1 s = a"
    "N b \<le> N (lowpt2 s)"
    "t \<in> Directed_Multigraph.V (edges_from_fun I)"
    "t \<noteq> a"
    "t \<noteq> b"
    "t \<notin> D s"
  using assms
  by (auto simp add: is_type_1_pair'_def dest: is_type_1_pairD)

lemma (in steps_1_2_3_high) is_type_1_pair'I:
  assumes "b \<noteq> a"
  assumes "s \<noteq> a"
  assumes "b \<rightarrow> s"
  assumes "lowpt1 s = a"
  assumes "N b \<le> N (lowpt2 s)"
  assumes "t \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "t \<noteq> a"
  assumes "t \<noteq> b"
  assumes "t \<notin> D s"
  shows "is_type_1_pair' a b"
  using assms
  by (auto simp add: is_type_1_pair'_def intro: is_type_1_pairI)

definition (in steps_1_2_3_high) first_child :: "'b \<Rightarrow> 'b option" where
  "first_child u \<equiv> case (children u) of Nil \<Rightarrow> None | (v # vs) \<Rightarrow> Some v"

lemma (in steps_1_2_3_high) first_child_cong:
  shows "first_child v = (if children v = [] then None else Some (hd (children v)))"
  by (cases "children v") (simp_all add: first_child_def)+

lemma (in steps_1_2_3_high) first_child_eq_SomeD:
  assumes "first_child u = Some v"
  shows
    "children u \<noteq> []"
    "children u ! 0 = v"
  using assms
  by (fastforce simp add: first_child_cong hd_conv_nth split: if_splits(2))+

(* QUESTION: Should we use trancl instead of rtrancl? *)
definition (in steps_1_2_3_high) first_descendant :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "first_descendant u v \<equiv> (u, v) \<in> {(u, v). first_child u = Some v}\<^sup>*"

lemma (in steps_1_2_3_high) first_descendant_refl:
  shows "first_descendant v v"
  by (simp add: first_descendant_def)

lemma (in steps_1_2_3_high) first_child_imp_tree_arc':
  assumes "first_child u = Some v"
  shows "u \<rightarrow> v"
  using assms
  by (auto simp add: first_child_cong dest: hd_in_set mem_childrenD split: if_splits(2))

lemma (in steps_1_2_3_high) first_descendant_imp_tree_path:
  assumes "first_descendant u v"
  shows "u \<rightarrow>\<^sup>* v"
proof -
  have "{(u, v). first_child u = Some v}\<^sup>* \<subseteq> {(u, v). u \<rightarrow> v}\<^sup>*"
    using first_child_imp_tree_arc'
    by (intro rtrancl_mono) blast
  thus ?thesis
    using assms
    by (auto simp add: first_descendant_def tree_path_def)
qed

lemma (in steps_1_2_3_high) first_descendant_transitive:
  assumes "first_descendant u v"
  assumes "first_descendant v w"
  shows "first_descendant u w"
  using assms
  by (simp add: first_descendant_def)

lemma (in steps_1_2_3_high) first_descendant_imp_walk_aux:
assumes "u \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "first_descendant u v"
  shows "\<exists>p. walk (edges_from_map T) p u v \<and> (\<forall>e\<in>set p. first_child (tail e) = Some (head e))"
  using assms(2)
  unfolding first_descendant_def
  using assms(1)
proof (induct rule: rtrancl.induct)
  case (rtrancl_refl a)
  thus ?case
    by (auto simp add: V_eq dest: walk_Nil)
next
  case (rtrancl_into_rtrancl u v w)
  then obtain p where
    "walk (edges_from_map T) p u v"
    "\<forall>e\<in>set p. first_child (tail e) = Some (head e)"
    by blast
  moreover obtain e where
    "e \<in> (edges_from_map T)"
    "Directed_Multigraph.endpoints e = (v, w)"
    using rtrancl_into_rtrancl.hyps(3)
    by (fastforce simp add: tree_arc'_iff_mem_endpoints dest: first_child_imp_tree_arc')
  ultimately have
    "walk (edges_from_map T) (p @ [e]) u w"
    "\<forall>e\<in>set (p @ [e]). first_child (tail e) = Some (head e)"
    using rtrancl_into_rtrancl.hyps(3)
    by (auto simp add: walk_snoc_iff head_def tail_def)
  thus ?case
    by fast
qed

lemma (in steps_1_2_3_high) first_descendant_imp_walk:
  assumes "u \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "first_descendant u v"
  obtains p where
    "walk (edges_from_map T) p u v"
    "\<forall>e\<in>set p. first_child (tail e) = Some (head e)"
  using assms
  by (blast dest: first_descendant_imp_walk_aux)

lemma (in steps_1_2_3_high) first_descendant_if_walk:
  assumes "walk (edges_from_map T) p u v"
  assumes "\<forall>e\<in>set p. first_child (tail e) = Some (head e)"
  shows "first_descendant u v"
  using assms
proof (induct p arbitrary: u)
  case Nil
  thus ?case
    using first_descendant_refl
    by (simp add: walk_Nil_iff)
next
  case (Cons e es)
  let ?x = "head e"
  show ?case
  proof (rule first_descendant_transitive[where ?v = ?x], goal_cases)
    case 1
    then show ?case
      using Cons.prems
      by (auto simp add: walk_Cons_iff first_descendant_def)
  next
    case 2
    show ?case
      using Cons.prems
      by (auto simp add: walk_Cons_iff intro: Cons.hyps)
  qed
qed

lemma (in steps_1_2_3_high) first_descendant_pref:
  assumes "first_descendant u w"
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "v \<rightarrow>\<^sup>* w"
  shows "first_descendant u v"
  using assms
proof (cases "u \<in> Directed_Multigraph.V (edges_from_fun I)")
  case True
  then obtain p where
    p: "walk (edges_from_map T) p u w"
    "\<forall>e\<in>set p. first_child (tail e) = Some (head e)"
    using assms(1)
    by (elim first_descendant_imp_walk)
  obtain p1 where
    p1: "walk (edges_from_map T) p1 u v"
    using True assms(2)
    by (auto simp add: V_eq elim: tree_path_imp_walk)
  then obtain p2 where
    p2: "walk (edges_from_map T) p2 v w"
    using assms(3)
    by (blast dest: last_vertex_mem_V elim: tree_path_imp_walk)
  have "p1 @ p2 = p"
    using p1 p2 p(1)
    by (intro unique_walk_3)
  thus ?thesis
    using p1 p(2)
    by (force dest: first_descendant_if_walk)
next
  case False
  hence "u = v"
    using assms(2)
    by (auto simp add: tree_path_non_empty_tree_path_cong dest: hd_non_empty_tree_path_mem_V)
  thus ?thesis
    using first_descendant_refl
    by auto
qed

lemma (in steps_1_2_3_high) first_descendant_suf:
  assumes "first_descendant u w"
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "v \<rightarrow>\<^sup>* w"
  shows "first_descendant v w"
  using assms
proof (cases "u \<in> Directed_Multigraph.V (edges_from_fun I)")
  case True
  then obtain p where
    p: "walk (edges_from_map T) p u w"
    "\<forall>e\<in>set p. first_child (tail e) = Some (head e)"
    using assms(1)
    by (elim first_descendant_imp_walk)
  obtain p1 where
    p1: "walk (edges_from_map T) p1 u v"
    using True assms(2)
    by (auto simp add: V_eq elim: tree_path_imp_walk)
  then obtain p2 where
    p2: "walk (edges_from_map T) p2 v w"
    using assms(3)
    by (blast dest: last_vertex_mem_V elim: tree_path_imp_walk)
  have "p1 @ p2 = p"
    using p1 p2 p(1)
    by (intro unique_walk_3)
  thus ?thesis
    using p2 p(2)
    by (force dest: first_descendant_if_walk)
next
  case False
  hence "v = w"
    using assms(2, 3)
    by (auto simp add: tree_path_non_empty_tree_path_cong dest: hd_non_empty_tree_path_mem_V)
  thus ?thesis
    using first_descendant_refl
    by auto
qed

definition (in steps_1_2_3_high) is_type_2_pair where
  "is_type_2_pair a b s \<equiv>
   N a \<noteq> 1 \<and>
   (\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')) \<and>
   s \<noteq> b \<and>
   a \<rightarrow> s \<and>
   first_descendant s b \<and>
   (\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y)"

lemma (in steps_1_2_3_high_2) is_type_2_pairD:
  assumes "is_type_2_pair a b s"
  shows
    "a \<in> Directed_Multigraph.V (edges_from_fun I)"
    "N a \<noteq> 1"
    "b \<in> Directed_Multigraph.V (edges_from_fun I)"
    "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')"
    "s \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<noteq> a"
    "s \<noteq> b"
    "a \<rightarrow> s"
    "s \<rightarrow>\<^sup>* b"
    "first_descendant s b"
    "\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y"
proof -
  show
    "N a \<noteq> 1"
    "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')"
    "s \<noteq> b"
    "a \<rightarrow> s"
    "first_descendant s b"
    "\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y"
    using assms
    by (simp_all add: is_type_2_pair_def)
  thus
    "a \<in> Directed_Multigraph.V (edges_from_fun I)"
    "b \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<noteq> a"
    "s \<rightarrow>\<^sup>* b"
    by
      (force
        simp add: tree_path_non_empty_tree_path_cong
        dest: tail_tree_arc'_mem_V first_descendant_imp_tree_path last_non_empty_tree_path_mem_V head_tree_arc'_mem_V N_less_if_tree_arc')+
qed

lemma (in steps_1_2_3_high) is_type_2_pairI:
  assumes "N a \<noteq> 1"
  assumes "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')"
  assumes "s \<noteq> b"
  assumes "a \<rightarrow> s"
  assumes "first_descendant s b"
  assumes "\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y"
  shows "is_type_2_pair a b s"
  using assms
  by (simp add: is_type_2_pair_def)

definition (in steps_1_2_3_high) is_type_2_pair' where
  "is_type_2_pair' a b \<equiv> \<exists>s. is_type_2_pair a b s"

lemma (in steps_1_2_3_high_2) is_type_2_pair'D:
  assumes "is_type_2_pair' a b"
  shows
    "a \<in> Directed_Multigraph.V (edges_from_fun I)"
    "N a \<noteq> 1"
    "b \<in> Directed_Multigraph.V (edges_from_fun I)"
    "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')"
  using assms
  by (auto simp add: is_type_2_pair'_def dest: is_type_2_pairD(1-4))

lemma (in steps_1_2_3_high_2) is_type_2_pair'E:
  assumes "is_type_2_pair' a b"
  obtains s where
    "s \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<noteq> a"
    "s \<noteq> b"
    "a \<rightarrow> s"
    "s \<rightarrow>\<^sup>* b"
    "first_descendant s b"
    "\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y"
  using assms
  by (auto simp add: is_type_2_pair'_def dest: is_type_2_pairD(5-))

lemma (in steps_1_2_3_high) is_type_2_pair'I:
  assumes "N a \<noteq> 1"
  assumes "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')"
  assumes "s \<noteq> b"
  assumes "a \<rightarrow> s"
  assumes "first_descendant s b"
  assumes "\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y"
  shows "is_type_2_pair' a b"
  using assms
  unfolding is_type_2_pair'_def
  by (blast intro: is_type_2_pairI)

lemma (in steps_1_2_3_high) lemma_5_1:
  shows "length (children r) \<le> 1"
  sorry

lemma (in steps_1_2_3_high) lemma_5_2:
  assumes "u \<noteq> r"
  assumes "u \<rightarrow> v"
  shows "N (lowpt1 v) < N u"
  sorry

lemma (in steps_1_2_3_high) lemma_5_3:
  assumes "r \<rightarrow> v"
  shows "lowpt1 v = r"
  sorry

lemma idk_10:
  fixes xs :: "nat list"
  assumes "n < sum_list xs"
  obtains i where
    "i < length xs"
    "sum_list (drop (Suc i) xs) \<le> n"
    "n < sum_list (drop i xs)"
  using assms
proof (induct xs arbitrary: i)
  case Nil
  thus ?case
    by force
next
  case (Cons x xs)
  thus ?case
    (* TODO: Beautify. *)
    by (metis drop0 drop_Suc_Cons length_Cons linorder_le_less_linear not_less_eq zero_less_Suc)
qed

lemma (in steps_1_2_3_high_2) lemma_6_i_1:
  assumes "u \<in> Directed_Multigraph.V (edges_from_fun I)"
  shows "D u = {x \<in> Directed_Multigraph.V (edges_from_fun I). N u \<le> N x \<and> N x < N u + ND u}"
  using assms
proof (induct "ND u" arbitrary: u rule: less_induct)
  case less
  { fix v
    assume assm: "v \<in> set (children u)"
    have
      "ND v < ND u"
      "v \<in> Directed_Multigraph.V (edges_from_fun I)"
    proof -
      show "ND v < ND u"
        using finite_D assm
        by
          (fastforce
            simp add: ND_def
            dest: mem_childrenD non_empty_tree_path_if_tree_arc' D_subsetI_2
            intro: psubset_card_mono)
      show "v \<in> Directed_Multigraph.V (edges_from_fun I)"
        using assm
        by (blast dest: mem_childrenD head_tree_arc'_mem_V)
    qed }
  hence
    "D u =
     {u} \<union>
     (\<Union>i<length (children u).
         {x \<in> Directed_Multigraph.V (edges_from_fun I).
          N (children u ! i) \<le> N x \<and> N x < N (children u ! i) + ND (children u ! i)})"
    by (auto simp add: D_children_cong[of u, symmetric] less.hyps set_conv_nth)
  also have
    "... =
     {u} \<union>
     (\<Union>i<length (children u).
         {x \<in> Directed_Multigraph.V (edges_from_fun I).
          N u + sum_list (map ND (agublagu_geq u (i + 1))) + 1 \<le> N x \<and>
          N x < N u + sum_list (map ND (agublagu_geq u (i + 1))) + 1 + ND (children u ! i)})"
    using less.prems
    by (simp add: P2)
  also have
    "... =
     {u} \<union>
     (\<Union>i<length (children u).
         {x \<in> Directed_Multigraph.V (edges_from_fun I).
          N u + sum_list (map ND (agublagu_geq u (i + 1))) + 1 \<le> N x \<and>
          N x < N u + sum_list (map ND (agublagu_geq u i)) + 1})"
  proof -
    { fix i
      assume "i < length (children u)"
      hence
        "sum_list (map ND (agublagu_geq u i)) =
         sum_list (map ND (children u ! i # agublagu_geq u (i + 1)))"
        by (simp add: agublagu_geq_def Cons_nth_drop_Suc)
      hence
        "sum_list (map ND (agublagu_geq u (i + 1))) + ND (children u ! i) =
         sum_list (map ND (agublagu_geq u i))"
        by fastforce }
    thus ?thesis
      by fastforce
  qed
  also have
    "... =
     {u} \<union>
     {x \<in> Directed_Multigraph.V (edges_from_fun I). N u + 1 \<le> N x \<and> N x < N u + ND u}"
    (is "{u} \<union> ?A = {u} \<union> ?B")
  proof -
    { fix x
      assume assm: "x \<in> ?A"
      then obtain i where
        "N x < N u + sum_list (map ND (agublagu_geq u i)) + 1"
        by blast
      hence "N x < N u + ND u"
        by (simp add: idk_5[of u i, symmetric])
      hence "x \<in> ?B"
        using assm
        by force }
    moreover { fix x
      assume assm: "x \<in> ?B"
      hence "N x < N u + sum_list (map ND (children u)) + 1"
        by (simp add: ND_children_cong[symmetric])
      hence "N x - N u - 1 < sum_list (map ND (children u))"
        using assm
        by fastforce
      then obtain i where
        "i < length (children u)"
        "N u + sum_list (map ND (agublagu_geq u (i + 1))) + 1 \<le> N x"
        "N x < N u + sum_list (map ND (agublagu_geq u i)) + 1"
        using assm
        by
          (fastforce
            simp add: agublagu_geq_def
            elim: idk_10[of "N x - N u - 1" "map ND (children u)", unfolded drop_map])
      hence "x \<in> ?A"
        using assm
        by blast }
    ultimately show ?thesis
      by blast
  qed
  also have
    "... =
     {x \<in> Directed_Multigraph.V (edges_from_fun I). N u \<le> N x \<and> N x < N u + ND u}"
    using less.prems ND_greater_0
    by (fastforce simp add: N_eq_iff[symmetric])
  finally show ?case
    .
qed

lemma (in steps_1_2_3_high_2) lemma_6_i_2_aux:
  assumes "u \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "first_descendant u v"
  shows
    "D v =
     {x \<in> Directed_Multigraph.V (edges_from_fun I). N v \<le> N x \<and> N x < N u + ND u}"
proof -
  obtain p where
    "walk (edges_from_map T) p u v"
    "\<forall>e\<in>set p. first_child (tail e) = Some (head e)"
    using assms
    by (elim first_descendant_imp_walk)
  thus ?thesis
    using assms
  proof (induct p arbitrary: u)
    case Nil
    thus ?case
      using walk_Nil_iff
      by (simp add: walk_Nil_iff lemma_6_i_1)
  next
    case (Cons e es)
    let ?x = "head e"
    have
      "D v =
       {x \<in> Directed_Multigraph.V (edges_from_fun I).
        N v \<le> N x \<and> N x < N (head e) + ND ?x}"
    proof (intro Cons.hyps)
      show
        "walk (edges_from_map T) es ?x v"
        "\<forall>e\<in>set es. first_child (tail e) = Some (head e)"
        "?x \<in> Directed_Multigraph.V (edges_from_fun I)"
        using Cons.prems(1, 2)
        by (auto simp add: walk_Cons_iff V_eq dest: head_mem_V)
      thus "first_descendant ?x v"
        by (intro first_descendant_if_walk)
    qed
    thm P2
    also have
      "... =
       {x \<in> Directed_Multigraph.V (edges_from_fun I).
        N v \<le> N x \<and> N x < N u + sum_list (map ND (agublagu_geq u 1)) + 1 + ND ?x}"
    proof -
      have "?x = children u ! 0"
        using Cons.prems(1, 2)
        by (auto simp add: walk_Cons_iff dest: first_child_eq_SomeD(2))
      thus ?thesis
        using Cons.prems(3)
        by (simp add: P2)
    qed
    also have
      "... =
       {x \<in> Directed_Multigraph.V (edges_from_fun I).
        N v \<le> N x \<and> N x < N u + sum_list (map ND (agublagu_geq u 1)) + 1 + sum_list (map ND (agublagu_less u 1))}"
    proof -
      have
        "children u \<noteq> []"
        "children u ! 0 = ?x"
        using Cons.prems(1, 2)
        by (auto simp add: walk_Cons_iff dest: first_child_eq_SomeD)
      hence "sum_list (map ND (agublagu_less u 1)) = ND ?x"
        by (simp add: agublagu_less_def take_Suc hd_conv_nth)
      thus ?thesis
        by presburger
    qed
    also have
      "... =
       {x \<in> Directed_Multigraph.V (edges_from_fun I). N v \<le> N x \<and> N x < N u + ND u}"
      unfolding idk_5[of u 1, symmetric]
      by fastforce
    finally show ?case
      .
  qed
qed

lemma (in steps_1_2_3_high_2) lemma_6_i_2:
  assumes "u \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "first_descendant u v"
  shows
    "D u - D v =
     {x \<in> Directed_Multigraph.V (edges_from_fun I). N u \<le> N x \<and> N x < N v}"
proof -
  have
    "D u - D v =
     {x \<in> Directed_Multigraph.V (edges_from_fun I). N u \<le> N x \<and> N x < N u + ND u} -
     {x \<in> Directed_Multigraph.V (edges_from_fun I). N v \<le> N x \<and> N x < N u + ND u}"
    using assms first_descendant_refl
    by (simp add: lemma_6_i_2_aux)
  also have
    "... =
     {x \<in> Directed_Multigraph.V (edges_from_fun I). N u \<le> N x \<and> N x < N v}"
  proof -
    have "v \<in> D u"
      using assms(2)
      by (auto simp add: mem_D_iff_tree_path dest: first_descendant_imp_tree_path)
    hence "N v < N u + ND u"
      using assms(1) first_descendant_refl
      by (simp add: lemma_6_i_2_aux)
    thus ?thesis
      by force
  qed
  finally show ?thesis
    .
qed

(**)

(* TODO: Move. *)
lemma (in steps_1_2_3_high_2) neq_rI:
  assumes "u \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "N u < N v"
  shows "v \<noteq> r"
  using assms P1
  by (fastforce dest: N_geq_1)

lemma (in steps_1_2_3_high_3) idk_52:
  assumes "u \<rightarrow> v"
  shows "Multigraph.V (Multigraph.E G (D v)) \<subseteq> D v \<union> {u} \<union> {x. tree_path_snoc_frond' v x}"
proof -
  { fix x
    assume
      assm: "x \<in> Multigraph.V (Multigraph.E G (D v))"
      "\<not> v \<rightarrow>\<^sup>* x"
      "x \<noteq> u"
      "\<not> tree_path_snoc_frond' v x"
    obtain y where
      y: "{x, y} \<in> Multigraph.endpoints ` G"
      "v \<rightarrow>\<^sup>* y"
    proof -
      obtain y where
        "{x, y} \<in> Multigraph.endpoints ` Multigraph.E G (D v)"
        "y \<in> D v"
        using assm(1-2)
        by
          (auto
            simp add: undirect_P_eq_G[symmetric] mem_D_iff_tree_path[symmetric]
            intro: mem_V_EE)
      thus ?thesis
        using E_subset
        by (fastforce simp add: mem_D_iff_tree_path intro: that)
    qed
    hence False
    proof (cases rule: cases_edge)
      case tree_arc_1
      hence "v = y"
        using y(2) assm(2)
        by (blast dest: unique_tree_path_3)
      thus ?thesis
        using tree_arc_1 assms assm(3)
        by (blast dest: unique_tree_path_4)
    next
      case tree_arc_2
      thus ?thesis
        using y(2) assm(2)
        by (blast dest: tree_path_if_tree_arc' tree_path_trans)
    next
      case frond_1
      hence "y \<rightarrow>\<^sup>* x"
        by (blast dest: frond'_imp_tree_path)
      thus ?thesis
        using y(2) assm(2)
        by (blast dest: tree_path_trans)
    next
      case frond_2
      thus ?thesis
        using y(2) assm(4)
        by (blast dest: tree_path_snoc_frond'I)
    qed }
  thus ?thesis
    by (fastforce simp add: mem_D_iff_tree_path)
  thm P3
qed

lemma (in steps_1_2_3_high_2) P3_2:
  shows "linorder_class.sorted (map (\<lambda>e. \<phi> (tail e) (head e)) (incidence I v))"
  using P3
  by (simp add: sorted_map)

(* TODO: Beautify. *)
lemma idk_99:
  assumes "linorder_class.sorted l"
  assumes "x \<in> set l"
  shows "hd l \<le> x"
  using assms
  by (metis list.exhaust list.sel(1) nle_le set_ConsD sorted_simps(2) sorted_wrt1)

(* TODO: Beautify. *)
lemma idk_100:
  assumes "linorder_class.sorted (map f l)"
  assumes "x \<in> set l"
  shows "f (hd l) \<le> f x"
  using assms
  by (metis empty_iff idk_99 image_eqI list.map_sel(1) list.set(1) list.set_map)

lemma (in steps_1_2_3_high_2) lowpt1_cong:
  assumes "v \<in> Directed_Multigraph.V (edges_from_fun I)"
  shows
    "lowpt1 v =
     (case incidence I v of
      [] \<Rightarrow> v |
      e # es \<Rightarrow> if tree_arc e then lowpt1 (head e) else head e)"
proof -
  show ?thesis
  proof (cases "incidence I v")
    case Nil
    { assume "lowpt1 v \<noteq> v"
      then consider
        (frond') "frond' v (lowpt1 v)" |
        (tree_arc') "\<exists>x. v \<rightarrow> x \<and> tree_path_snoc_frond' x (lowpt1 v)"
        using lowpt1
        by (blast dest: tree_path_snoc_frond'_10)
      hence False
        (* TODO: Beautify. *)
        using Nil
        by (cases) (metis Directed_Multigraph.endpoints_def edge_iff empty_iff fst_conv list.set(1) mem_edges_from_funE snd_conv tail_def tail_eq)+ }
    thus ?thesis
      using Nil
      by auto
  next
    case (Cons e es)
    show ?thesis
    proof (cases "tree_arc e")
      case True
      hence tree_arc': "v \<rightarrow> head e"
        unfolding tail_eq[OF list.set_intros(1)[of e es, unfolded Cons[symmetric]], symmetric]
        by (intro tree_arc'I)
      consider
        (eq) "lowpt1 v = v" |
        (frond') "frond' v (lowpt1 v)" |
        (tree_arc'_2) "\<exists>x. v \<rightarrow> x \<and> tree_path_snoc_frond' x (lowpt1 v)"
        using lowpt1
        by (blast dest: tree_path_snoc_frond'_10)
      hence "lowpt1 v = lowpt1 (head e)"
      proof (cases)
        case eq
        have "v = r"
          using tree_arc' lemma_5_2
          by (fastforce simp add: eq dest: N_lowpt1_tree_arc')
        thus ?thesis
          using tree_arc' eq
          by (blast dest: lemma_5_3)
      next
        case frond'
        then obtain e' where
          e': "Directed_Multigraph.endpoints e' = (v, lowpt1 v)"
          "e' \<in> set (incidence I v)"
          by
            (fastforce
              simp add: Directed_Multigraph.endpoints_def tail_def
              dest: mem_edges_from_funD
              elim: frond'E)
        have "3 * N (lowpt1 (head e)) \<le> 3 * N (lowpt1 v) + 1"
        proof -
          have "3 * N (lowpt1 (head e)) \<le> \<phi> (tail e) (head e)"
            using True
            by (auto simp add: \<phi>_def intro: tree_arc'I)
          also have "... \<le> \<phi> (tail e') (head e')"
            using P3_2 e'(2)
            by (fastforce simp add: Cons dest: idk_100)
          also have "... = \<phi> v (lowpt1 v)"
            using e'(1)
            by (simp add: tail_def head_def Directed_Multigraph.endpoints_def)
          also have "... = 3 * N (lowpt1 v) + 1"
            using frond'
            by (auto simp add: \<phi>_def dest: frond'_imp_tree_path no_closed_tree_path_3)
          finally show ?thesis
            .
        qed
        hence "N (lowpt1 (head e)) = N (lowpt1 v)"
          using tree_arc'
          by (force dest: N_lowpt1_tree_arc')
        thus ?thesis
          using True assms
          by (force simp add: N_eq_iff dest: head_tree_arc'_mem_V lowpt1_mem_V tree_arc'I)
      next
        case tree_arc'_2
        then obtain x where
          x: "v \<rightarrow> x"
          "tree_path_snoc_frond' x (lowpt1 v)"
          by fast
        then obtain e' where
          e': "Directed_Multigraph.endpoints e' = (v, x)"
          "e' \<in> set (incidence I v)"
          by
            (fastforce
              simp add: Directed_Multigraph.endpoints_def tail_def
              dest: tree_arc_imp_edge mem_edges_from_funD
              elim: tree_arc'E)
        have "3 * N (lowpt1 (head e)) \<le> 3 * N (lowpt1 v) + 2"
        proof -
          have "3 * N (lowpt1 (head e)) \<le> \<phi> (tail e) (head e)"
            using True
            by (auto simp add: \<phi>_def intro: tree_arc'I)
          also have "... \<le> \<phi> (tail e') (head e')"
            using P3_2 e'(2)
            by (fastforce simp add: Cons dest: idk_100)
          also have "... = \<phi> v x"
            using e'(1)
            by (simp add: tail_def head_def Directed_Multigraph.endpoints_def)
          also have "... \<le> 3 * N (lowpt1 x) + 2"
            using x(1)
            by (simp add: \<phi>_def)
          also have "... \<le> 3 * N (lowpt1 v) + 2"
            using x(2)
            by (force dest: N_lowpt1_least)
          finally show ?thesis
            .
        qed
        hence "N (lowpt1 (head e)) = N (lowpt1 v)"
          using tree_arc'
          by (force dest: N_lowpt1_tree_arc')
        thus ?thesis
          using True assms
          by (force simp add: N_eq_iff dest: head_tree_arc'_mem_V lowpt1_mem_V tree_arc'I)
      qed
      thus ?thesis  
        using Cons True
        by auto
    next
      case False
      have "e \<in> edges_from_fun I"
        using list.set_intros(1)[of e es]
        by (auto simp add: Cons[symmetric] intro: mem_edges_from_funI)
      hence frond': "frond' v (head e)"
        unfolding tail_eq[OF list.set_intros(1)[of e es, unfolded Cons[symmetric]], symmetric]
        using False
        by (auto simp add: frond_def intro: frond'I)
      consider
        (eq) "lowpt1 v = v" |
        (frond'_2) "frond' v (lowpt1 v)" |
        (tree_arc') "\<exists>x. v \<rightarrow> x \<and> tree_path_snoc_frond' x (lowpt1 v)"
        using lowpt1
        by (blast dest: tree_path_snoc_frond'_10)
      hence "lowpt1 v = head e"
      proof (cases)
        case eq
        have "N (lowpt1 v) \<le> N (head e)"
          using frond'
          by (intro N_lowpt1_frond')
        moreover have "N (head e) \<le> N (lowpt1 v)"
          using frond'
          by (auto simp add: eq dest: frond'_imp_tree_path N_leq_if_tree_path)
        ultimately show ?thesis
          using assms frond'
          by (auto simp add: eq N_eq_iff dest: head_frond'_mem_V)
      next
        case frond'_2
        then obtain e' where
          e': "Directed_Multigraph.endpoints e' = (v, lowpt1 v)"
          "e' \<in> set (incidence I v)"
          by
            (fastforce
              simp add: Directed_Multigraph.endpoints_def tail_def
              dest: mem_edges_from_funD
              elim: frond'E)
        have "3 * N (head e) \<le> 3 * N (lowpt1 v) + 1"
        proof -
          have "3 * N (head e) \<le> \<phi> (tail e) (head e)"
            unfolding tail_eq[OF list.set_intros(1)[of e es, unfolded Cons[symmetric]]]
            using frond'
            by (auto simp add: \<phi>_def dest: frond'_imp_tree_path no_closed_tree_path_3)
          also have "... \<le> \<phi> (tail e') (head e')"
            using P3_2 e'(2)
            by (fastforce simp add: Cons dest: idk_100)
          also have "... = \<phi> v (lowpt1 v)"
            using e'(1)
            by (simp add: tail_def head_def Directed_Multigraph.endpoints_def)
          also have "... = 3 * N (lowpt1 v) + 1"
            using frond'_2
            by (auto simp add: \<phi>_def dest: frond'_imp_tree_path no_closed_tree_path_3)
          finally show ?thesis
            .
        qed
        hence "N (head e) = N (lowpt1 v)"
          using frond'
          by (force dest: N_lowpt1_frond')
        thus ?thesis
          using frond' frond'_2
          by (force simp add: N_eq_iff dest: head_frond'_mem_V)
      next
        case tree_arc'
        then obtain x where
          x: "v \<rightarrow> x"
          "tree_path_snoc_frond' x (lowpt1 v)"
          by fast
        then obtain e' where
          e': "Directed_Multigraph.endpoints e' = (v, x)"
          "e' \<in> set (incidence I v)"
          by
            (fastforce
              simp add: Directed_Multigraph.endpoints_def tail_def
              dest: tree_arc_imp_edge mem_edges_from_funD
              elim: tree_arc'E)
        have "3 * N (head e) \<le> 3 * N (lowpt1 v) + 2"
        proof -
          have "3 * N (head e) \<le> \<phi> (tail e) (head e)"
            unfolding tail_eq[OF list.set_intros(1)[of e es, unfolded Cons[symmetric]]]
            using frond'
            by (auto simp add: \<phi>_def dest: frond'_imp_tree_path no_closed_tree_path_3)
          also have "... \<le> \<phi> (tail e') (head e')"
            using P3_2 e'(2)
            by (fastforce simp add: Cons dest: idk_100)
          also have "... = \<phi> v x"
            using e'(1)
            by (simp add: tail_def head_def Directed_Multigraph.endpoints_def)
          also have "... \<le> 3 * N (lowpt1 x) + 2"
            using x(1)
            by (simp add: \<phi>_def)
          also have "... \<le> 3 * N (lowpt1 v) + 2"
            using x(2)
            by (force dest: N_lowpt1_least)
          finally show ?thesis
            .
        qed
        hence "N (head e) = N (lowpt1 v)"
          using frond'
          by (force dest: N_lowpt1_frond')
        thus ?thesis
          using frond' assms
          by (force simp add: N_eq_iff dest: head_frond'_mem_V lowpt1_mem_V)
      qed
      thus ?thesis
        using Cons False
        by fastforce
    qed
  qed
qed

function (in steps_1_2_3_high) (domintros) bla where
  "bla v =
   (case incidence I v of 
    [] \<Rightarrow> [] |
    e # es \<Rightarrow> e # (if tree_arc e then bla (head e) else []))"
  by simp+

(* TODO: Rename. *)
lemma (in steps_1_2_3_high) xoxoxo:
  assumes "incidence I v = e # es"
  assumes "tree_arc e"
  shows "v \<rightarrow> head e"
  using assms
  unfolding tail_eq[OF list.set_intros(1)[of e es, unfolded assms(1)[symmetric]], symmetric]
  by (intro tree_arc'I)

(* TODO: Rename. *)
lemma (in steps_1_2_3_high) xixixi:
  assumes "(v, u) \<in> {(v, u). \<exists>e es. v = head e \<and> incidence I u = e # es \<and> tree_arc e}"
  shows "u \<rightarrow> v"
  using assms
  by (blast intro: xoxoxo)

(* TODO: Rename. *)
lemma (in steps_1_2_3_high) xexexe:
  assumes "(v, u) \<in> {(v, u). \<exists>e es. v = head e \<and> incidence I u = e # es \<and> tree_arc e}\<^sup>+"
  shows "u \<rightarrow>\<^sup>+ v"
  using assms
proof (induct rule: trancl.induct)
  case (r_into_trancl)
  thus ?case
    by (intro xixixi non_empty_tree_path_if_tree_arc')
next
  case (trancl_into_trancl)
  thus ?case
    by (blast intro: xixixi non_empty_tree_path_imp_tree_path non_empty_tree_pathI_2)
qed

definition swap where
  "swap p = (snd p, fst p)"

(* TODO: Rename. *)
lemma (in steps_1_2_3_high) xaxaxa:
  shows "wf {(v, u). \<exists>e es. v = head e \<and> incidence I u = e # es \<and> tree_arc e}" (is "wf ?r")
proof (rule finite_acyclic_wf, goal_cases)
  case 1
  let ?r' = "{(u, v). \<exists>e es. v = head e \<and> incidence I u = e # es \<and> tree_arc e}"
  have "finite ?r'"
    using finite_edges_from_map
    by (fastforce simp add: tree_arc'_iff_mem_endpoints dest: xoxoxo intro: finite_surj)
  moreover have "?r = swap ` ?r'"
    by (force simp add: swap_def)
  ultimately show ?case
    by fastforce
next
  case 2
  { fix x
    assume "(x, x) \<in> ?r\<^sup>+"
    hence False
      by (blast dest: xexexe non_empty_tree_path_imp_neq) }
  thus ?case
    by (auto simp add: acyclic_def)
qed

lemma (in steps_1_2_3_high) bla_dom:
  shows "bla_dom v"
  using xaxaxa
  by (auto simp add: wfP_def bla_rel.simps intro: accp_wfPD)

lemma (in steps_1_2_3_high) bla_simps:
  shows
    "bla v =
     (case incidence I v of 
      [] \<Rightarrow> [] |
      e # es \<Rightarrow> e # (if tree_arc e then bla (head e) else []))"
  using bla_dom
  by (intro bla.psimps)

lemma (in steps_1_2_3_high) bla_induct:
  assumes
    "\<And>v. (\<And>e es. incidence I v = e # es \<Longrightarrow> tree_arc e \<Longrightarrow> P (head e)) \<Longrightarrow> P v"
  shows "P v"
  using bla_dom
proof (rule bla.pinduct, goal_cases)
  case 1
  thus ?case
    by (blast intro: assms)
qed

lemma (in steps_1_2_3_high) bla_empty_iff:
  shows "bla v = [] \<longleftrightarrow> incidence I v = []"
  by (simp add: bla_simps split: list.split)

lemma (in steps_1_2_3_high_2) walk_butlast_bla:
  assumes "v \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "lowpt1 v \<noteq> v"
  shows "Directed_Walk.walk (edges_from_map T) (butlast (bla v)) v (tail (last (bla v)))"
  using assms
proof (induct rule: bla_induct[where ?v = v])
  case (1 v)
  show ?case
  proof (cases "incidence I v")
    case Nil
    thus ?thesis
      using "1.prems"
      by (simp add: lowpt1_cong)
  next
    case (Cons e es)
    show ?thesis
    proof (cases "tree_arc e")
      case True
      hence head_e_mem_V: "head e \<in> Directed_Multigraph.V (edges_from_fun I)"
        by (intro tree_arc_imp_edge head_mem_V)
      have lowpt1_head_e_neq: "lowpt1 (head e) \<noteq> head e"
      proof (standard, goal_cases)
        case 1
        have tree_arc': "tail e \<rightarrow> head e"
          using True
          by (intro tree_arc'I)
        have "N (lowpt1 (head e)) \<le> N (tail e)"
        proof (cases "tail e = r")
          case True
          thus ?thesis
            using tree_arc'
            by (simp add: lemma_5_3)
        next
          case False
          thus ?thesis
            using tree_arc'
            by (fastforce dest: lemma_5_2)
        qed
        thus ?case
          using tree_arc'
          by (auto simp add: 1 dest: N_less_if_tree_arc')
      qed
      hence "Directed_Walk.walk (edges_from_map T) (butlast (bla (head e))) (head e) (tail (last (bla (head e))))"
        using Cons True head_e_mem_V
        by (intro "1.hyps")
      moreover have "bla (head e) \<noteq> []"
        using head_e_mem_V lowpt1_head_e_neq
        by (auto simp add: bla_empty_iff lowpt1_cong)
      ultimately show ?thesis
        using True Cons "1.prems"(1)
        by (simp add: bla_simps Directed_Walk.walk_Cons_iff tree_arc_iff_edge tail_eq[symmetric])
    next
      case False
      hence "bla v = [e]"
        using "1.prems"(1) Cons
        by (simp add: bla_simps)
      thus ?thesis
        using Cons "1.prems"(1)
        by (simp add: tail_eq V_eq Directed_Walk.walk_Nil_iff)
    qed
  qed
qed

lemma (in steps_1_2_3_high_2) bla_10:
  assumes "v \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "lowpt1 v \<noteq> v"
  shows "\<forall>e\<in>set (butlast (bla v)). first_child (tail e) = Some (head e)"
  using assms
proof (induct rule: bla_induct)
  case (1 v)
  show ?case
  proof (cases "incidence I v")
    case Nil
    thus ?thesis
      using "1.prems"
      by (simp add: lowpt1_cong)
  next
    case (Cons e es)
    show ?thesis
    proof (cases "tree_arc e")
      case True
      have "lowpt1 (head e) \<noteq> head e"
      proof (standard, goal_cases)
        case 1
        have tree_arc': "tail e \<rightarrow> head e"
          using True
          by (intro tree_arc'I)
        have "N (lowpt1 (head e)) \<le> N (tail e)"
        proof (cases "tail e = r")
          case True
          thus ?thesis
            using tree_arc'
            by (simp add: lemma_5_3)
        next
          case False
          thus ?thesis
            using tree_arc'
            by (fastforce dest: lemma_5_2)
        qed
        thus ?case
          using tree_arc'
          by (auto simp add: 1 dest: N_less_if_tree_arc')
      qed
      hence "\<forall>e\<in>set (butlast (bla (head e))). first_child (tail e) = Some (head e)"
        using Cons True
        by (intro tree_arc_imp_edge head_mem_V "1.hyps")
      moreover have "first_child (tail e) = Some (head e)"
        unfolding tail_eq[OF list.set_intros(1)[of e es, unfolded Cons[symmetric]]]
        using Cons True
        by (simp add: first_child_def children_def)
      ultimately show ?thesis
        using Cons "1.prems"(1)
        by (simp add: bla_simps)
    next
      case False
      thus ?thesis
        using "1.prems"(1) Cons
        by (simp add: bla_simps)
    qed
  qed
qed

lemma (in steps_1_2_3_high_2) frond_last_bla:
  assumes "v \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "lowpt1 v \<noteq> v"
  shows "frond (last (bla v))"
  using assms
proof (induct rule: bla_induct)
  case (1 v)
  show ?case
  proof (cases "incidence I v")
    case Nil
    thus ?thesis
      using "1.prems"
      by (simp add: lowpt1_cong)
  next
    case (Cons e es)
    show ?thesis
    proof (cases "tree_arc e")
      case True
      hence head_e_mem_V: "head e \<in> Directed_Multigraph.V (edges_from_fun I)"
        by (intro tree_arc_imp_edge head_mem_V)
      have lowpt1_head_e_neq: "lowpt1 (head e) \<noteq> head e"
      proof (standard, goal_cases)
        case 1
        have tree_arc': "tail e \<rightarrow> head e"
          using True
          by (intro tree_arc'I)
        have "N (lowpt1 (head e)) \<le> N (tail e)"
        proof (cases "tail e = r")
          case True
          thus ?thesis
            using tree_arc'
            by (simp add: lemma_5_3)
        next
          case False
          thus ?thesis
            using tree_arc'
            by (fastforce dest: lemma_5_2)
        qed
        thus ?case
          using tree_arc'
          by (auto simp add: 1 dest: N_less_if_tree_arc')
      qed
      hence "frond (last (bla (head e)))"
        using Cons True head_e_mem_V
        thm "1.hyps"
        by (intro "1.hyps")
      moreover have "bla (head e) \<noteq> []"
        using head_e_mem_V lowpt1_head_e_neq
        by (auto simp add: bla_empty_iff lowpt1_cong)
      ultimately show ?thesis
        using True Cons "1.prems"(1)
        by (simp add: bla_simps)
    next
      case False
      have "e \<in> edges_from_fun I"
        using list.set_intros(1)[of e es, unfolded Cons[symmetric]]
        by (auto simp add: edges_from_fun_def)
      thus ?thesis
        using "1.prems"(1) Cons False
        by (simp add: bla_simps frond_iff_not_tree_arc)
    qed
  qed
qed

lemma (in steps_1_2_3_high_2) head_last_bla_eq_lowpt1:
  assumes "v \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "lowpt1 v \<noteq> v"
  shows "head (last (bla v)) = lowpt1 v"
  using assms
proof (induct rule: bla_induct[where ?v = v])
  case (1 v)
  show ?case
  proof (cases "incidence I v")
    case Nil
    thus ?thesis
      using "1.prems"
      by (simp add: lowpt1_cong)
  next
    case (Cons e es)
    show ?thesis
    proof (cases "tree_arc e")
      case True
      hence head_e_mem_V: "head e \<in> Directed_Multigraph.V (edges_from_fun I)"
        by (intro tree_arc_imp_edge head_mem_V)
      have lowpt1_head_e_neq: "lowpt1 (head e) \<noteq> head e"
      proof (standard, goal_cases)
        case 1
        have tree_arc': "tail e \<rightarrow> head e"
          using True
          by (intro tree_arc'I)
        have "N (lowpt1 (head e)) \<le> N (tail e)"
        proof (cases "tail e = r")
          case True
          thus ?thesis
            using tree_arc'
            by (simp add: lemma_5_3)
        next
          case False
          thus ?thesis
            using tree_arc'
            by (fastforce dest: lemma_5_2)
        qed
        thus ?case
          using tree_arc'
          by (auto simp add: 1 dest: N_less_if_tree_arc')
      qed
      hence "head (last (bla (head e))) = lowpt1 (head e)"
        using Cons True head_e_mem_V
        by (intro "1.hyps")
      moreover have "bla (head e) \<noteq> []"
        using head_e_mem_V lowpt1_head_e_neq
        by (auto simp add: bla_empty_iff lowpt1_cong)
      ultimately show ?thesis
        using Cons "1.prems"(1)
        by (simp add: bla_simps lowpt1_cong)
    next
      case False
      have "e \<in> edges_from_fun I"
        using list.set_intros(1)[of e es, unfolded Cons[symmetric]]
        by (auto simp add: edges_from_fun_def)
      thus ?thesis
        using "1.prems"(1) Cons False
        by (simp add: bla_simps lowpt1_cong)
    qed
  qed
qed

lemma (in steps_1_2_3_high_2) first_descendant_1:
  assumes "v \<in> Directed_Multigraph.V (edges_from_fun I)"
  assumes "lowpt1 v \<noteq> v"
  obtains x where
    "first_descendant v x"
    "frond' x (lowpt1 v)"
proof
  let ?x = "tail (last (bla v))"
  show "first_descendant v ?x"
    using assms
    by (blast dest: walk_butlast_bla bla_10 first_descendant_if_walk)
  show "frond' ?x (lowpt1 v)"
  proof -
    have "frond' ?x (head (last (bla v)))"
      using assms
      by (intro frond_last_bla frond'I)
    thus ?thesis
      using assms
      by (simp add: head_last_bla_eq_lowpt1)
  qed
qed

(* TODO: Move. *)
lemma
  assumes "length l \<le> 1"
  assumes "x \<in> set l"
  shows "l = [x]"
  using assms
  by (cases l) simp+

lemma (in steps_1_2_3_high_3) idk_101:
  assumes "a \<rightarrow>\<^sup>* b"
  assumes "b \<rightarrow> b'"
  assumes "D b' \<notin> connected_components (idk_4 G {a, b})"
  obtains v where
    "v \<in> Directed_Multigraph.V (edges_from_fun I)"
    "v \<noteq> a"
    "v \<noteq> b"
    "v \<notin> D b'"
    "tree_path_snoc_frond' b' v"
proof -
  let ?G = "idk_4 G {a, b}"
  have "connected' ?G (D b')"
  proof (rule connected'_1, goal_cases)
    case 1
    show ?case
      using assms(2)
      by (fastforce simp add: undirect_P_eq_G[symmetric] dest: head_tree_arc'_mem_V connected'_D)
  next
    case 2
    have "b \<notin> D b'"
      using assms(2)
      by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path_3)
    moreover have "a \<notin> D b'"
      using assms(1, 2)
      by (auto simp add: mem_D_iff_tree_path dest: tree_path_trans no_closed_tree_path_3)
    ultimately show ?case
      by fast
  qed
  then obtain u v where
    "u \<in> D b'"
    "{u, v} \<in> Multigraph.endpoints ` G"
    "v \<in> Directed_Multigraph.V (edges_from_fun I)"
    "v \<noteq> a"
    "v \<noteq> b"
    "v \<notin> D b'"
    using assms(3) idk_4_subset
    by (blast elim: connected'_not_connected_componentE_2[of ?G, unfolded V_idk_4_eq V_E_I_eq_V_G[symmetric]])
  thus ?thesis
    using assms(2)
    by (blast dest: idk_52 intro: mem_V_EI that)
qed

lemma (in steps_1_2_3_high_2) lemma_7_aux:
  assumes "u \<rightarrow> v"
  assumes "x \<noteq> u"
  assumes "tree_path_snoc_frond' v x"
  assumes "N u \<le> N x"
  shows "v \<rightarrow>\<^sup>* x"
proof (rule ccontr, goal_cases)
  case 1
  hence "x \<rightarrow>\<^sup>* v"
    using assms(3)
    by (auto dest: tree_path_snoc_frond'_imp_tree_path)
  hence "x \<rightarrow>\<^sup>* u"
    using assms(1) D_refl 1
    by (auto dest: unique_tree_path_3)
  hence "N x \<le> N u"
    by (intro N_leq_if_tree_path)
  moreover have "N x \<noteq> N u"
    using assms
    by
      (fastforce
        simp add: N_eq_iff[symmetric]
        dest: last_tree_path_snoc_frond'_mem_V tail_tree_arc'_mem_V)
  ultimately show ?case
    using assms(4)
    by fastforce
qed

lemma (in steps_1_2_3_high_3) lemma_7_aux_2:
  assumes "a \<rightarrow> v"
  assumes "v \<rightarrow>\<^sup>* b"
  assumes "b' \<in> set (agublagu_geq b (i\<^sub>0 a b))"
  assumes "D b' \<notin> connected_components (idk_4 G {a, b})"
  obtains x where
    "x \<in> D v - D b"
    "tree_path_snoc_frond' b' x"
proof -
  have "a \<rightarrow>\<^sup>* b"
    using assms(1-2)
    by (blast dest: tree_path_if_tree_arc' tree_path_trans)
  then obtain x where
    x: "x \<in> Directed_Multigraph.V (edges_from_fun I)"
    "x \<noteq> a"
    "x \<noteq> b"
    "x \<notin> D b'"
    "tree_path_snoc_frond' b' x"
    using assms(3-4)
    by (blast dest: mem_agublagu_geq_imp_mem_children mem_childrenD elim: idk_101)
  have "v \<rightarrow>\<^sup>* x"
    using assms(1) x(2)
  proof (rule lemma_7_aux, goal_cases)
    case 1
    show ?case
      using assms(2-3) x(5)
      by (auto dest: mem_agublagu_geq_imp_mem_children mem_childrenD tree_path_if_tree_arc' tree_path_trans tree_path_snoc_frond'I_2)
  next
    case 2
    have "N a \<le> N (lowpt1 b')"
      using P3 assms(3)
      by (intro sorted_wrt_lowpt1_children mem_agublagu_geqD)
    thus ?case
      using x(5)
      by (fastforce dest: N_lowpt1_least)
  qed
  moreover have "\<not> b \<rightarrow>\<^sup>* x"
  proof -
    have "x \<rightarrow>\<^sup>* b'"
      using x(4-5)
      by (auto simp add: mem_D_iff_tree_path dest: tree_path_snoc_frond'_imp_tree_path)
    then consider
      "x \<rightarrow>\<^sup>* b" |
      "x = b'"
      using assms(3)
      by (blast dest: mem_agublagu_geq_imp_mem_children mem_childrenD unique_tree_path_3)
    thus ?thesis
    proof (cases)
      case 1
      thus ?thesis
        using x(3)
        by (intro no_closed_tree_path_2)
    next
      case 2
      thus ?thesis
        using D_refl x(4)
        by simp
    qed
  qed
  ultimately show ?thesis
    using x(5)
    by (auto simp add: mem_D_iff_tree_path intro: that)
qed

(* TODO: Generalize graph. *)
lemma (in steps_1_2_3_high_3) lemma_7_aux_5:
  assumes "connected' (idk_4 G {a, b}) X"
  assumes "\<forall>y\<in>Y. connected' (idk_4 G {a, b}) (D y)"
  assumes "\<forall>y\<in>Y. \<exists>x\<in>X. tree_path_snoc_frond' y x"
  shows "connected' (idk_4 G {a, b}) (X \<union> \<Union> (D ` Y))"
  using assms(1)
proof (rule connected'_100, goal_cases)
  case 1
  show ?case
    sorry
next
  case 2
  show ?case
    using assms(2)
    by fastforce
next
  case 3
  { fix y
    assume assm: "y \<in> Y"
    then obtain x where
      "x \<in> X"
      "x \<notin> {a, b}"
      "tree_path_snoc_frond' y x"
      using assms(1, 3) V_idk_4_subset
      by (fast dest: connected'_subset)
    moreover then obtain z where
      "z \<in> D y"
      "z \<notin> {a, b}"
      "frond' z x"
      using assms(2) assm V_idk_4_subset
      by
        (fastforce
          simp add: mem_D_iff_tree_path
          dest: connected'_subset
          elim: tree_path_snoc_frond'E)
    ultimately have "\<exists>x\<in>X. \<exists>z\<in>D y. {z, x} \<in> Multigraph.endpoints ` idk_4 G {a, b}"
      by (fastforce simp add: edge_iff_3 intro: mem_endpoints_idk_4I) }
  thus ?case
    by fast
qed

lemma (in steps_1_2_3_high_3) lemma_6_ii:
  assumes a_less_b: "N a < N b"
  assumes is_separation_pair: "is_separation_pair G a b"
\<comment> \<open>
We don't need this assumption because if there is even a single edge, then the lemma follows
immediately.
\<close>
  assumes not_is_multiple_edge: "\<not> is_multiple_edge G {a, b}"
  shows "a \<rightarrow>\<^sup>+ b"
proof (rule ccontr, goal_cases)
  case assm: 1
  let ?G = "idk_4 G {a, b}"
  let ?A = "D r - D a - D b"
  let ?B = "?A \<union> \<Union> (D ` set (children a))"
  let ?C = "?B \<union> \<Union> (D ` set (children b))"
  have
    a_mem_V: "a \<in> Directed_Multigraph.V (edges_from_fun I)" and
    b_mem_V: "b \<in> Directed_Multigraph.V (edges_from_fun I)"
    using is_separation_pair
    by (auto simp add: V_E_I_eq_V_G dest: separation_pair_mem_V)
  have V_cong: "Multigraph.V G = ?C \<union> {a, b}"
  proof -
    have "D r = D r - D a \<union> \<Union> (D ` set (children a)) \<union> {a}"
      using a_mem_V D_children_cong
      by (blast dest: tree_path_if_mem_V D_subsetI)
    moreover have "D r = D r - D b \<union> \<Union> (D ` set (children b)) \<union> {b}"
      using b_mem_V D_children_cong
      by (blast dest: tree_path_if_mem_V D_subsetI)
    ultimately show ?thesis
      using D_children_cong
      by (auto simp add: V_E_I_eq_V_G D_r_eq_V)
  qed
  have C_mem_connected_components: "?C \<in> connected_components ?G"
  proof -
    obtain C1 where
      C1: "C1 \<in> connected_components ?G"
      "?C \<subseteq> C1"
    proof -
      have "connected' ?G ?C"
      proof (rule lemma_7_aux_5, goal_cases)
        case 1
        show ?case
        proof (rule lemma_7_aux_5, goal_cases)
          case 1
          show ?case
          proof (rule connected'_1, goal_cases)
            case 1
            then show ?case sorry
          next
            case 2
            show ?case
              using D_refl
              by force
          qed
        next
          case 2
          show ?case
          proof (standard, goal_cases)
            case (1 y)
            thus ?case
            proof (intro connected'_1, goal_cases)
              case 1
              hence "y \<in> Directed_Multigraph.V (edges_from_fun I)"
                by (fast dest: mem_childrenD head_tree_arc'_mem_V)
              thus ?case
                by (auto simp add: undirect_P_eq_G dest: connected'_D)
            next
              case 2
              hence "a \<notin> D y"
                by (fastforce simp add: mem_D_iff_tree_path dest: mem_childrenD no_closed_tree_path_3)
              moreover have "b \<notin> D y"
                using 2 assm
                by (auto simp add: mem_D_iff_tree_path dest: mem_childrenD intro: non_empty_tree_pathI_2)
              ultimately show ?case
                by blast
            qed
          qed
        next
          case 3
          show ?case
          proof (standard, goal_cases)
            case (1 y)
            have "lowpt1 y \<in> ?A"
            proof (standard, standard)
              show "lowpt1 y \<in> D r"
                using 1
                by
                  (auto
                    simp add: mem_D_iff_tree_path
                    dest: mem_childrenD head_tree_arc'_mem_V lowpt1_mem_V tree_path_if_mem_V)
              have "a \<noteq> r"
                using b_mem_V a_less_b assm
                by (fastforce simp add: tree_path_non_empty_tree_path_cong dest: tree_path_if_mem_V)
              hence "N (lowpt1 y) < N a"
                using 1
                by (blast dest: mem_childrenD lemma_5_2)
              thus
                "lowpt1 y \<notin> D a"
                "lowpt1 y \<notin> D b"
                using a_less_b
                by (auto simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path)
            qed
            moreover hence "tree_path_snoc_frond' y (lowpt1 y)"
              using lowpt1 1
              by (force simp add: mem_D_iff_tree_path dest: mem_childrenD tree_path_if_tree_arc')
            ultimately show ?case
              by blast
          qed
        qed
      next
        case 2
        show ?case
        proof (standard, goal_cases)
          case (1 y)
          thus ?case
          proof (intro connected'_1, goal_cases)
            case 1
            hence "y \<in> Directed_Multigraph.V (edges_from_fun I)"
              by (fast dest: mem_childrenD head_tree_arc'_mem_V)
            thus ?case
              by (auto simp add: undirect_P_eq_G dest: connected'_D)
          next
            case 2
            hence "b \<notin> D y"
              by (fastforce simp add: mem_D_iff_tree_path dest: mem_childrenD no_closed_tree_path_3)
            moreover have "a \<notin> D y"
              using 2 a_less_b
              by
                (fastforce
                  simp add: mem_D_iff_tree_path
                  dest: mem_childrenD tree_path_if_tree_arc' tree_path_trans N_leq_if_tree_path)
            ultimately show ?case
              by blast
          qed
        qed
      next
        case 3
        show ?case
        proof (standard, goal_cases)
          case (1 y)
          have "b \<noteq> r"
            using a_mem_V a_less_b
            by (fastforce dest: neq_rI)
          hence lowpt1_y_less_b: "N (lowpt1 y) < N b"
            using 1
            by (blast dest: mem_childrenD lemma_5_2)
          have tree_path_snoc_frond'_y_lowpt1_y: "tree_path_snoc_frond' y (lowpt1 y)"
          proof (rule ccontr)
            assume "\<not> tree_path_snoc_frond' y (lowpt1 y)"
            hence "lowpt1 y = y"
              using lowpt1
              by blast
            thus False
              using 1 lowpt1_y_less_b
              by (fastforce dest: mem_childrenD N_less_if_tree_arc')
          qed
          moreover have "lowpt1 y \<in> ?A"
          proof (standard, standard)
            show "lowpt1 y \<in> D r"
              using 1
              by
                (auto
                  simp add: mem_D_iff_tree_path
                  dest: mem_childrenD head_tree_arc'_mem_V lowpt1_mem_V tree_path_if_mem_V)
            show "lowpt1 y \<notin> D b"
              using lowpt1_y_less_b a_less_b
              by (auto simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path)
            show "lowpt1 y \<notin> D a"
            proof
              assume "lowpt1 y \<in> D a"
              moreover have
                "lowpt1 y \<rightarrow>\<^sup>* y"
                using tree_path_snoc_frond'_y_lowpt1_y 1 lowpt1_y_less_b
                by (fastforce dest: tree_path_snoc_frond'_imp_tree_path mem_childrenD tree_path_if_tree_arc' tree_path_trans N_leq_if_tree_path)
              ultimately have "a \<rightarrow>\<^sup>* y"
                by (auto simp add: mem_D_iff_tree_path dest: tree_path_trans)
              thus False
                using 1 a_less_b N_less_if_tree_arc' assm
                by (fastforce simp add: tree_path_non_empty_tree_path_cong dest: mem_childrenD unique_tree_path_3)
            qed
          qed
          ultimately show ?case
            by blast
        qed
      qed
      thus ?thesis
        by (blast intro: connected'_subset_connected_component that)
    qed
    have "C1 = ?C"
    proof -
      { fix x
        assume
          assm: "x \<in> C1"
          "x \<notin> ?C"
        have "x \<in> Multigraph.V G - {a, b}"
          using V_idk_4_subset C1(1) assm(1)
          by (fast dest: connected_component_subset_2)
        hence False
          using assm(2)
          by (simp add: V_cong) }
      thus ?thesis
        using C1(2)
        by blast
    qed
    thus ?thesis
      using C1(1)
      by blast
  qed
  then obtain C2 where
    C2: "C2 \<in> connected_components ?G"
    "C2 \<noteq> ?C"
    using is_separation_pair not_is_multiple_edge
    by (elim separation_class_99)
  then obtain x where
    x: "x \<in> C2"
    "x \<notin> ?C"
    using C_mem_connected_components connected_component_non_empty_2[of C2 ?G] connected_components_disjoint[of ?C ?G C2]
    by auto
  have "x \<in> Multigraph.V G - {a, b}"
    using V_idk_4_subset C2(1) x(1)
    by (fast dest: connected_component_subset_2)
  thus ?case
    using x(2)
    by (simp add: V_cong)
qed

lemma (in steps_1_2_3_high_3) is_type_1_pair_if:
  assumes non_empty_tree_path_a_b: "a \<rightarrow>\<^sup>+ b"
  assumes tree_arc'_b_s: "b \<rightarrow> s"
  assumes D_s_mem_connected_components: "D s \<in> connected_components (idk_4 G {a, b})"
  assumes t_mem_V: "t \<in> Multigraph.V (idk_4 G {a, b})"
  assumes t_not_mem_D_s: "t \<notin> D s"
  shows "is_type_1_pair a b s t"
proof (rule is_type_1_pairI)
  have
    a_mem_V: "a \<in> Directed_Multigraph.V (edges_from_fun I)" and
    b_mem_V: "b \<in> Directed_Multigraph.V (edges_from_fun I)" and
    a_less_b: "N a < N b"
    using non_empty_tree_path_a_b
    by (blast dest: hd_non_empty_tree_path_mem_V last_non_empty_tree_path_mem_V N_less_if_non_empty_tree_path)+
  have
    s_mem_V: "s \<in> Directed_Multigraph.V (edges_from_fun I)" and
    b_less_s: "N b < N s"
    using tree_arc'_b_s
    by (blast intro: tail_tree_arc'_mem_V head_tree_arc'_mem_V N_less_if_tree_arc')+
  
  show "b \<noteq> a"
    using a_less_b
    by fast
  show "b \<rightarrow> s"
    using tree_arc'_b_s
    .
  show "s \<noteq> a"
    using a_less_b b_less_s
    by fastforce
  show lowpt1_s_eq_a: "lowpt1 s = a"
  proof -
    have "lowpt1 s \<in> D s \<union> {a, b}"
    proof (cases "lowpt1 s = s")
      case True
      thus ?thesis
        using D_refl
        by auto
    next
      case False
      then obtain x where
        "s \<rightarrow>\<^sup>* x"
        "frond' x (lowpt1 s)"
        using lowpt1
        by (blast elim: tree_path_snoc_frond'E)
      hence "lowpt1 s \<in> Multigraph.V (Multigraph.E G (D s))"
        by (auto simp add: mem_D_iff_tree_path edge_iff_3 intro: mem_V_EI)
      thus ?thesis
        using D_s_mem_connected_components
        by (blast dest: connected_component_10)
    qed
    moreover have
      "lowpt1 s \<noteq> b"
      "lowpt1 s \<notin> D s"
    proof -
      have
        "b \<noteq> r"
        "s \<noteq> r"
        using a_mem_V a_less_b b_mem_V b_less_s
        by (blast dest: neq_rI)+
      hence
        "N (lowpt1 s) < N b"
        "N (lowpt1 s) < N s"
        using tree_arc'_b_s b_less_s
        by (fastforce dest: lemma_5_2)+
      thus
        "lowpt1 s \<noteq> b"
        "lowpt1 s \<notin> D s"
        by (auto simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path)
    qed
    ultimately show ?thesis
      by blast
  qed
  show "N b \<le> N (lowpt2 s)"
  proof -
    have "lowpt2 s \<in> D s \<union> {a, b}"
    proof (cases "lowpt2 s = s")
      case True
      thus ?thesis
        using D_refl
        by simp
    next
      case False
      then obtain x where
        "s \<rightarrow>\<^sup>* x"
        "frond' x (lowpt2 s)"
        using lowpt2
        by (blast elim: tree_path_snoc_frond'E)
      hence "lowpt2 s \<in> Multigraph.V (Multigraph.E G (D s))"
        by (auto simp add: mem_D_iff_tree_path edge_iff_3 intro: mem_V_EI)
      thus ?thesis
        using D_s_mem_connected_components
        by (blast dest: connected_component_10)
    qed
    hence "lowpt2 s \<in> D s \<union> {b}"
      using D_refl lowpt1_s_eq_a
      by (fastforce simp add: lowpt2_eq_lowpt1_iff)
    hence "lowpt2 s \<in> D b"
      using tree_arc'_b_s D_refl
      by (fastforce dest: tree_path_if_tree_arc' D_subsetI)
    thus ?thesis
      by (force simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path)
  qed
  show
    "t \<in> Directed_Multigraph.V (edges_from_fun I)"
    "t \<noteq> a"
    "t \<noteq> b"
    "t \<notin> D s"
    using t_mem_V t_not_mem_D_s
    by (simp_all add: V_idk_4_eq V_E_I_eq_V_G)
qed

lemma (in steps_1_2_3_high_3) is_type_1_pair_imp:
  assumes "is_type_1_pair a b s t"
  shows
    "a \<rightarrow>\<^sup>+ b"
    "b \<rightarrow> s"
    "D s \<in> connected_components (idk_4 G {a, b})"
    "t \<in> Multigraph.V (idk_4 G {a, b})"
    "t \<notin> D s"
proof -
  have
    "a \<in> Directed_Multigraph.V (edges_from_fun I)"
    "b \<in> Directed_Multigraph.V (edges_from_fun I)" and
    b_neq_a: "b \<noteq> a" and
    s: "s \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<noteq> a"
    "s \<noteq> b"
    "b \<rightarrow> s"
    "lowpt1 s = a"
    "N b \<le> N (lowpt2 s)" and
    "t \<in> Directed_Multigraph.V (edges_from_fun I)"
    "t \<noteq> a"
    "t \<noteq> b"
    "t \<notin> D s"
    using assms
    by (blast dest: is_type_1_pairD)+
  thus
    "b \<rightarrow> s"
    "t \<in> Multigraph.V (idk_4 G {a, b})"
    "t \<notin> D s"
    by (simp_all add: V_E_I_eq_V_G V_idk_4_eq)
  show non_empty_tree_path_a_b: "a \<rightarrow>\<^sup>+ b"
  proof -
    have "a \<rightarrow>\<^sup>* s"
    proof (rule ccontr, goal_cases)
      case 1
      have "tree_path_snoc_frond' s a"
        using s(2, 5) lowpt1
        by force
      hence "s \<rightarrow>\<^sup>* a"
        using 1
        by (fast dest: tree_path_snoc_frond'_imp_tree_path)
      hence "s \<rightarrow>\<^sup>+ a"
        using s(2)
        by (simp add: tree_path_non_empty_tree_path_cong)
      hence "N s < N (lowpt1 s)"
        using s(2, 5)
        by (blast dest: N_less_if_non_empty_tree_path)
      thus ?case
        using N_lowpt1_leq[of s]
        by force
    qed
    hence "a \<rightarrow>\<^sup>* b"
      using s(2, 4)
      by (blast dest: unique_tree_path_3)
    thus ?thesis
      using b_neq_a
      by (simp add: tree_path_non_empty_tree_path_cong)
  qed
  show "D s \<in> connected_components (idk_4 G {a, b})"
  proof (rule ccontr, goal_cases)
    let ?G = "idk_4 G {a, b}"
    case 1
    then obtain y where
      y: "y \<in> Directed_Multigraph.V (edges_from_fun I)"
      "y \<noteq> a"
      "y \<noteq> b"
      "y \<notin> D s"
      "tree_path_snoc_frond' s y"
      using non_empty_tree_path_a_b s(4)
      by (blast dest: non_empty_tree_path_imp_tree_path elim: idk_101)
    have "y \<in> D s"
      using s(4-6) y(2, 3, 5)
      by (fastforce simp add: mem_D_iff_tree_path dest: N_lowpt2_leq lemma_7_aux)
    thus ?case
      using y(4)
      by blast
  qed
qed

lemma (in steps_1_2_3_high_3) is_type_1_pair_iff:
  shows
    "is_type_1_pair a b s t \<longleftrightarrow>
     a \<rightarrow>\<^sup>+ b \<and>
     b \<rightarrow> s \<and>
     D s \<in> connected_components (idk_4 G {a, b}) \<and>
     t \<in> Multigraph.V (idk_4 G {a, b}) \<and>
     t \<notin> D s"
  by (blast dest: is_type_1_pair_imp is_type_1_pair_if)

lemma (in steps_1_2_3_high_3) is_type_2_pair_if:
  assumes a_neq_r: "a \<noteq> r"
  assumes tree_arc'_a_s: "a \<rightarrow> s"
  assumes s_neq_b: "s \<noteq> b"
  assumes first_descendant_s_b: "first_descendant s b"
  assumes C_subset_Y: "connected_component (idk_4 G {a, b}) s \<subseteq> D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b)"
  shows "is_type_2_pair a b s"
proof (rule is_type_2_pairI)
  let ?G = "idk_4 G {a, b}"
  let ?C = "connected_component ?G s"
  let ?X = "D s - D b"
  let ?Y = "?X \<union> fukakyo_geq b (i\<^sub>0 a b)"
  have
    a_mem_V: "a \<in> Directed_Multigraph.V (edges_from_fun I)" and
    s_mem_V: "s \<in> Directed_Multigraph.V (edges_from_fun I)"
    using tree_arc'_a_s
    by (fast dest: tail_tree_arc'_mem_V head_tree_arc'_mem_V)+
  thus "N a \<noteq> 1"
    using r_mem_V a_neq_r
    by (simp add: N_eq_iff[symmetric] P1)
  have X_subset_C: "?X \<subseteq> ?C"
  proof -
    have "connected' ?G ?X"
    proof (rule connected'_1, goal_cases)
      case 1
      have "s \<notin> D b"
        using s_neq_b first_descendant_s_b
        by
          (auto
            simp add: mem_D_iff_tree_path
            dest: first_descendant_imp_tree_path no_closed_tree_path_2)
      thus ?case
        using s_mem_V
        by (auto simp add: undirect_P_eq_G[symmetric] dest: connected'_Diff_D)
    next
      case 2
      show ?case
        using tree_arc'_a_s D_refl
        by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path_3)
    qed
    moreover have "s \<in> ?X"
      using D_refl s_neq_b first_descendant_s_b
      by
        (auto
          simp add: mem_D_iff_tree_path
          dest: first_descendant_imp_tree_path no_closed_tree_path_2)
    ultimately show ?thesis
      by (blast dest: connected_component_71 elim: connected'_subset_connected_component)
  qed
  show "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')"
  proof -
    { fix b' x y
      assume
        assm: "frond' x y"
        "N a < N y"
        "N y < N b"
        "b \<rightarrow> b'"
        "b' \<rightarrow>\<^sup>* x"
      have "x \<in> fukakyo_geq b (i\<^sub>0 a b)"
      proof -
        have "x \<in> ?Y \<union> {a, b}"
        proof -
          have "x \<in> ?C \<union> {a, b}"
          proof (rule connected_component_1[of ?C G "{a, b}" y x], goal_cases)
            case 1
            have "s \<in> Multigraph.V ?G"
            proof -
              have "s \<in> Multigraph.V G"
                using tree_arc'_a_s
                by (auto simp add: V_E_I_eq_V_G dest: head_tree_arc'_mem_V)
              moreover have "s \<noteq> a"
                using tree_arc'_a_s
                by (blast dest: no_loop)
              ultimately show ?thesis
                using s_neq_b
                by (simp add: V_idk_4_eq)
            qed
            thus ?case
              by (simp add: connected_components_image_cong)
          next
            case 2
            have "y \<in> ?X"
            proof (standard, goal_cases)
              case 1
              show ?case
                unfolding mem_D_iff_tree_path
                using tree_arc'_a_s
              proof (rule lemma_7_aux, goal_cases)
                case 1
                show ?case
                  using assm(2)
                  by fast
              next
                case 2
                have "tree_path_snoc_frond' b y"
                  using assm(1, 4, 5)
                  by (auto dest: tree_path_if_tree_arc' tree_path_trans tree_path_snoc_frond'I)
                thus ?case
                  using first_descendant_s_b
                  by (blast dest: first_descendant_imp_tree_path tree_path_snoc_frond'I_2)
              next
                case 3
                show ?case
                  using assm(2)
                  by force
              qed
            next
              case 2
              show ?case
                using assm(3)
                by (auto simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path)
            qed
            thus ?case
              using X_subset_C
              by blast
          next
            case 3
            show ?case
              using assm(1)
              by (simp add: edge_iff_3)
          qed
          thus ?thesis
            using C_subset_Y
            by fast
        qed
        moreover have "x \<notin> ?X"
          using assm(4-5)
          by (auto simp add: mem_D_iff_tree_path dest: tree_path_if_tree_arc' tree_path_trans)
        moreover have "x \<noteq> a"
          using assm(1-2)
          by (fastforce dest: frond'_imp_tree_path N_leq_if_tree_path)
        moreover have "x \<noteq> b"
          using assm(4-5)
          by (blast dest: no_closed_tree_path_3)
        ultimately show ?thesis
          by fast
      qed
      hence "N a \<le> N (lowpt1 b')"
        using P3 sorted_wrt_lowpt1_children assm(4-5)
        by (simp add: mem_fukakyo_geq_1) }
    thus ?thesis
      by fast
  qed
  show "s \<noteq> b"
    using s_neq_b
    .
  show "a \<rightarrow> s"
    using tree_arc'_a_s
    .
  show "first_descendant s b"
    using first_descendant_s_b
    .
  show "\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y"
  proof -
    { fix x y
      assume
        assm: "frond' x y"
        "N s \<le> N x"
        "N x < N b"
      have "y \<in> D a"
      proof -
        have "y \<in> ?Y \<union> {a, b}"
        proof -
          have "y \<in> ?C \<union> {a, b}"
          proof (rule connected_component_1[of ?C G "{a, b}" x y], goal_cases)
            case 1
            have "s \<in> Multigraph.V ?G"
            proof -
              have "s \<in> Multigraph.V G"
                using tree_arc'_a_s
                by (auto simp add: V_E_I_eq_V_G dest: head_tree_arc'_mem_V)
              moreover have "s \<noteq> a"
                using tree_arc'_a_s
                by (blast dest: no_loop)
              ultimately show ?thesis
                using s_neq_b
                by (simp add: V_idk_4_eq)
            qed
            thus ?case
              by (simp add: connected_components_image_cong)
          next
            case 2
            have "x \<in> ?X"
              using s_mem_V first_descendant_s_b assm
              by (auto simp add: lemma_6_i_2 dest: tail_frond'_mem_V)
            thus ?case
              using X_subset_C
              by fast
          next
            case 3
            show ?case
              using assm(1)
              by (simp add: edge_iff_3)
          qed
          thus ?thesis
            using C_subset_Y
            by fast
        qed
        also have "... \<subseteq> D s \<union> {a}"
          using D_fukakyo_cong first_descendant_s_b
          by (fastforce dest: first_descendant_imp_tree_path D_subsetI)
        also have "... \<subseteq> D a"
          using tree_arc'_a_s D_refl
          by (fastforce dest: tree_path_if_tree_arc' D_subsetI)
        finally show ?thesis
          .
      qed
      hence "N a \<le> N y"
        by (auto simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path) }            
    thus ?thesis
      by blast
  qed
qed

lemma (in steps_1_2_3_high_3) is_type_2_pair_imp:
  assumes "is_type_2_pair a b s"
  shows
    "a \<noteq> r"
    "a \<rightarrow> s"
    "s \<noteq> b"
    "first_descendant s b"
    "connected_component (idk_4 G {a, b}) s \<subseteq> D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b)"
proof -
  let ?G = "idk_4 G {a, b}"
  let ?C = "connected_component ?G s"
  let ?X = "D s - D b"
  let ?Y = "?X \<union> fukakyo_geq b (i\<^sub>0 a b)"
  have
    "a \<in> Directed_Multigraph.V (edges_from_fun I)"
    "N a \<noteq> 1"
    "b \<in> Directed_Multigraph.V (edges_from_fun I)"
    "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')" and
    s: "s \<in> Directed_Multigraph.V (edges_from_fun I)"
    "s \<noteq> a"
    "s \<noteq> b"
    "a \<rightarrow> s"
    "s \<rightarrow>\<^sup>* b"
    "first_descendant s b"
    "\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y"
    using assms
    by (blast dest: is_type_2_pairD)+
  thus
    "a \<noteq> r"
    "a \<rightarrow> s"
    "s \<noteq> b"
    "first_descendant s b"
    by (auto simp add: P1)
  show "?C \<subseteq> ?Y"
  proof -
    { fix v
      assume
        assm: "v \<in> ?C"
        "v \<notin> ?Y"
      obtain p where
        "walk (idk_2 ?G ?C) p v s"
      proof -
        have "s \<in> Multigraph.V ?G"
          using s(1-3)
          by (simp add: V_idk_4_eq V_E_I_eq_V_G)
        hence
          "?C \<in> connected_components ?G"
          "s \<in> ?C"
          by (auto simp add: connected_components_image_cong dest: connected_component_refl)
        thus ?thesis
          using assm(1)
          by (blast elim: connected_component_72 intro: that)
      qed
      hence False
        using assm
      proof (induct p arbitrary: v)
        case Nil
        have "s \<in> ?Y"
          using D_refl s(3, 5)
          by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path_2)
        thus ?case
          using Nil(1, 3)
          by (simp add: walk_Nil_iff)
      next
        case (Cons e es)
        hence
          v: "v \<in> Directed_Multigraph.V (edges_from_fun I)"
          "v \<noteq> a"
          "v \<noteq> b"
          using connected_component_subset
          by (fastforce simp add: V_idk_4_eq V_E_I_eq_V_G)+
        let ?x = "other e v"
        show ?case
        proof (cases "?x \<in> ?Y")
          case True
          then consider
            (x_mem_X) "?x \<in> ?X" |
            (x_mem_fukakyo_geq) "?x \<in> fukakyo_geq b (i\<^sub>0 a b)"
            by fast
          thus ?thesis
          proof (cases)
            case x_mem_X
            have "{v, ?x} \<in> Multigraph.endpoints ` G"
              using Cons.prems(1) idk_2_subset idk_4_subset
              by (fastforce simp add: walk_Cons_iff other[symmetric])
            thus ?thesis
            proof (cases rule: cases_edge)
              case tree_arc_1
              have "v \<in> ?X"
              proof (standard, goal_cases)
                case 1
                show ?case
                proof (rule ccontr, goal_cases)
                  case 1
                  hence "\<not> s \<rightarrow>\<^sup>* v"
                    by (simp add: mem_D_iff_tree_path)
                  hence "s = ?x"
                    using tree_arc_1 x_mem_X
                    by (auto simp add: mem_D_iff_tree_path dest: unique_tree_path_3)
                  thus ?case
                    using tree_arc_1 s(4) v(2)
                    by (force dest: unique_tree_path_4)
                qed
              next
                case 2
                show ?case
                  using tree_arc_1 x_mem_X
                  by (auto simp add: mem_D_iff_tree_path dest: tree_path_if_tree_arc' tree_path_trans)
              qed
              thus ?thesis
                using Cons.prems(3)
                by fastforce
            next
              case tree_arc_2
              have "v \<in> ?X"
              proof (standard, goal_cases)
                case 1
                show ?case
                  using x_mem_X tree_arc_2
                  by (auto simp add: mem_D_iff_tree_path dest: tree_path_if_tree_arc' tree_path_trans)
              next
                case 2
                show ?case
                proof (rule ccontr, goal_cases)
                  case 1
                  hence "b \<rightarrow>\<^sup>* v"
                    by (simp add: mem_D_iff_tree_path)
                  thus ?case
                    using tree_arc_2 x_mem_X v(3)
                    by (auto simp add: mem_D_iff_tree_path dest: unique_tree_path_3)
                qed
              qed
              thus ?thesis
                using Cons.prems(3)
                by blast
            next
              case frond_1
              hence "v \<in> D s"
                using x_mem_X
                by (auto simp add: mem_D_iff_tree_path dest: frond'_imp_tree_path tree_path_trans)
              hence "v \<in> fukakyo_less b (i\<^sub>0 a b)"
                using Cons.prems(3) D_fukakyo_cong v(3)
                by blast
              then obtain b' where
                b': "b \<rightarrow> b'"
                "b' \<rightarrow>\<^sup>* v"
                "N (lowpt1 b') < N a"
                by (auto elim: mem_fukakyo_lessE)
              moreover have "N a \<le> N (lowpt1 b')"
              proof -
                have
                  "N a < N ?x"
                  "N ?x < N b"
                  using s(1, 4, 6) x_mem_X
                  by (auto simp add: lemma_6_i_2 dest: N_less_if_tree_arc')
                thus ?thesis
                  using assms frond_1 b'(1, 2)
                  by (blast dest: is_type_2_pairD(4))
              qed
              ultimately show ?thesis
                by force
            next
              case frond_2
              have "v \<in> ?X"
              proof (standard, goal_cases)
                case 1
                show ?case
                proof (rule ccontr, goal_cases)
                  case 1
                  hence assm: "\<not> s \<rightarrow>\<^sup>* v"
                    by (simp add: mem_D_iff_tree_path)
                  have "N v < N a"
                  proof -
                    have "tree_path_snoc_frond' s v"
                      using x_mem_X frond_2
                      by (auto simp add: mem_D_iff_tree_path intro: tree_path_snoc_frond'I)
                    hence "v \<rightarrow>\<^sup>* s"
                      using assm
                      by (blast dest: tree_path_snoc_frond'_imp_tree_path)
                    hence "v \<rightarrow>\<^sup>* a"
                      using s(4) assm
                      by (blast dest: unique_tree_path_3)
                    thus ?thesis
                      using v(2)
                      by (auto simp add: tree_path_non_empty_tree_path_cong dest: N_less_if_non_empty_tree_path)
                  qed
                  moreover have "N a \<le> N v"
                    using x_mem_X s(1, 6, 7) frond_2
                    by (fastforce dest: lemma_6_i_2)
                  ultimately show ?case
                    by simp
                qed
              next
                case 2
                show ?case
                  using frond_2 x_mem_X
                  by (auto simp add: mem_D_iff_tree_path dest: frond'_imp_tree_path tree_path_trans)
              qed
              thus ?thesis
                using Cons.prems(3)
                by blast
            qed
          next
            case x_mem_fukakyo_geq
            then obtain b' where
              b': "b \<rightarrow> b'"
              "b' \<rightarrow>\<^sup>* ?x"
              "N a \<le> N (lowpt1 b')"
              using P3
              by (blast dest: sorted_wrt_lowpt1_children elim: mem_fukakyo_geqE)
            have tree_path_snoc_frond'_b'_v: "tree_path_snoc_frond' b' v"
            proof -
              have "v \<in> Multigraph.V (Multigraph.E G (D b'))"
              proof (rule mem_V_EI[of ?x], goal_cases)
                case 1
                show ?case
                  using b'(2)
                  by (simp add: mem_D_iff_tree_path)
              next
                case 2
                have "e \<in> G"
                  using Cons.prems(1) idk_2_subset idk_4_subset
                  by (fastforce simp add: walk_Cons_iff)
                thus ?case
                  using Cons.prems(1)
                  by (auto simp add: walk_Cons_iff dest: other)
              qed
              hence "v \<in> D b' \<union> {b} \<union> {v. tree_path_snoc_frond' b' v}"
                using b'(1)
                by (auto simp add: dest: idk_52)
              thus ?thesis
                using b'(1, 3) Cons.prems(3) v(3)
                by (auto simp add: mem_D_iff_tree_path intro: mem_fukakyo_geqI)
            qed
            hence tree_path_snoc_frond'_s_v: "tree_path_snoc_frond' s v"
              using s(5) b'(1)
              by (auto dest: tree_path_if_tree_arc' tree_path_snoc_frond'I_2)
            hence tree_path_snoc_frond'_a_v: "tree_path_snoc_frond' a v"
              using s(4)
              by (auto dest: tree_path_if_tree_arc' tree_path_snoc_frond'I_2)

            have "v \<in> ?Y"
            proof -
              have "v \<in> D s"
                unfolding mem_D_iff_tree_path
                using s(4) v(2) tree_path_snoc_frond'_s_v
              proof (rule lemma_7_aux, goal_cases)
                case 1
                show ?case
                  using tree_path_snoc_frond'_b'_v b'(3)
                  by (fastforce dest: N_lowpt1_least)
              qed
              moreover
              { assume assm: "v \<in> D b"
                have "v \<in> D b'"
                  unfolding mem_D_iff_tree_path
                  using b'(1) v(3) tree_path_snoc_frond'_b'_v
                proof (rule lemma_7_aux, goal_cases)
                  case 1
                  then show ?case
                    using assm
                    by (auto simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path)
                qed }
              ultimately show ?thesis
                using b'(1, 3)
                by (auto simp add: mem_D_iff_tree_path intro: mem_fukakyo_geqI)
            qed
            thus ?thesis
              using Cons.prems(3)
              by blast
          qed
        next
          case False
          thus ?thesis
            using Cons.prems(1)
            by (auto simp add: walk_Cons_iff dest: other mem_idk_2D Cons.hyps)
        qed
      qed }
    thus ?thesis
      by blast
  qed
qed

lemma (in steps_1_2_3_high_3) is_type_2_pair_iff:
  shows
    "is_type_2_pair a b s \<longleftrightarrow>
     a \<noteq> r \<and>
     a \<rightarrow> s \<and>
     s \<noteq> b \<and>
     first_descendant s b \<and>
     connected_component (idk_4 G {a, b}) s \<subseteq> D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b)"
  by (blast dest: is_type_2_pair_imp is_type_2_pair_if)

lemma (in steps_1_2_3_high_2) lemma_7_aux_3:
  assumes a_eq_r: "a = r"
  assumes tree_arc'_a_v: "a \<rightarrow> v"
  shows "D r - D a \<union> \<Union> (D ` (set (children a) - {v})) \<union> fukakyo_less b (i\<^sub>0 a b) = {}"
proof -
  let ?A = "D r - D a"
  let ?B = "?A \<union> \<Union> (D ` (set (children a) - {v}))"
  have "?B = {}"
    using tree_arc'_a_v lemma_5_1
    unfolding a_eq_r
    by (cases "children r") (auto dest: mem_childrenI)
  moreover have "fukakyo_less b (i\<^sub>0 a b) = {}"
  proof (rule ccontr, goal_cases)
    case 1
    then obtain b' where
      "b \<rightarrow> b'"
      "N (lowpt1 b') < N a"
      by (blast elim: mem_fukakyo_lessE)
    moreover hence
      "lowpt1 b' \<in> Directed_Multigraph.V (edges_from_fun I)"
      by (intro head_tree_arc'_mem_V lowpt1_mem_V)
    ultimately show ?case
      by (fastforce simp add: a_eq_r dest: neq_rI)
  qed
  ultimately show ?thesis
    by blast
qed

lemma (in steps_1_2_3_high_3) lemma_7_aux_4:
  assumes no_D_mem_connected_components: "\<not> (\<exists>b'\<in>set (children b). D b' \<in> connected_components (idk_4 G {a, b}))"
  assumes tree_arc'_a_v: "a \<rightarrow> v"
  assumes v_eq_b: "v = b"
  shows "D v - D b \<union> fukakyo_geq b (i\<^sub>0 a b) = {}"
proof -
  let ?X = "D v - D b"
  have X_empty: "?X = {}"
    using v_eq_b
    by simp
  show ?thesis
  proof (cases "fukakyo_geq b (i\<^sub>0 a b) = {}")
    case True
    thus ?thesis
      using X_empty
      by blast
  next
    case False
    then obtain b' where
      "b' \<in> set (agublagu_geq b (i\<^sub>0 a b))"
      by (fastforce simp add: fukakyo_geq_def)
    then obtain x where
      "x \<in> ?X"
      using tree_arc'_a_v v_eq_b tree_path_refl no_D_mem_connected_components
      by (blast elim: lemma_7_aux_2 intro: mem_agublagu_geq_imp_mem_children)
    thus ?thesis
      using X_empty
      by blast
  qed
qed

lemma (in steps_1_2_3_high_3) lemma_7:
  assumes "N a < N b"
  shows
    "is_separation_pair G a b \<longleftrightarrow>
     is_type_1_pair' a b \<or>
     is_type_2_pair' a b \<or>
     is_multiple_edge G {a, b} \<and> 4 \<le> card G"
proof (standard, goal_cases)
  let ?G = "idk_4 G {a, b}"
  case 1
  hence
    a_mem_V: "a \<in> Directed_Multigraph.V (edges_from_fun I)" and
    b_mem_V: "b \<in> Directed_Multigraph.V (edges_from_fun I)"
    by (auto simp add: V_E_I_eq_V_G dest: separation_pair_mem_V)
  show ?case
  proof (cases "is_multiple_edge G {a, b}")
    case True
    thus ?thesis
      using 1
      by (auto intro: card_geq_4I)
  next
    case False
    show ?thesis
    proof (cases "\<exists>b'\<in>set (children b). D b' \<in> connected_components ?G")
      case True
      then obtain b' where
        "b \<rightarrow> b'"
        "D b' \<in> connected_components ?G"
        by (blast dest: mem_childrenD)
      moreover then obtain t where
        "t \<in> Multigraph.V ?G"
        "t \<notin> D b'"
        using 1 False
        by (auto simp add: V_idk_4_eq elim: separation_class_12)
      ultimately show ?thesis
        using assms 1 False
        by (auto simp add: is_type_1_pair'_def dest: lemma_6_ii intro: is_type_1_pair_if)
    next
      case no_D_mem_connected_components: False
      obtain v where
        v: "v \<in> Directed_Multigraph.V (edges_from_fun I)"
        "a \<rightarrow> v"
        "v \<rightarrow>\<^sup>* b"
        using assms 1 False
        by (fastforce dest: lemma_6_ii head_tree_arc'_mem_V elim: non_empty_tree_pathE)
      let ?A = "D r - D a"
      let ?B = "?A \<union> \<Union> (D ` (set (children a) - {v}))"
      let ?C = "?B \<union> fukakyo_less b (i\<^sub>0 a b)"
      let ?X = "D v - D b"
      let ?Y = "?X \<union> fukakyo_geq b (i\<^sub>0 a b)"
      have V_cong: "Multigraph.V G = ?C \<union> ?Y \<union> {a, b}"
      proof -
        have "Multigraph.V G = D r"
          by (simp add: V_E_I_eq_V_G D_r_eq_V)
        also have "... = ?A \<union> D a"
          using a_mem_V
          by (blast dest: tree_path_if_mem_V D_subsetI)
        also have "... = ?B \<union> D v \<union> {a}"
          using D_children_cong v(2)
          by (blast intro: mem_childrenI)
        also have "... = ?B \<union> ?X \<union> D b \<union> {a}"
          using v(3)
          by (blast dest: D_subsetI)
        also have "... = ?C \<union> ?Y \<union> {a, b}"
          using D_fukakyo_cong
          by auto
        finally show ?thesis
          .
      qed
      have
        C_mem_connected_components: "?C \<in> connected_components ?G" and
        Y_mem_connected_components: "?Y \<in> connected_components ?G" and
        Y_neq_C: "?Y \<noteq> ?C"
      proof -
        obtain C1 where
          C1: "C1 \<in> connected_components ?G"
          "?C \<subseteq> C1"
        proof (cases "a = r")
          case True
          hence "?C = {}"
            using v(2)
            by (intro lemma_7_aux_3)
          thus ?thesis
            using 1 False
            by (fast elim: separation_class_13 dest: that)
        next
          case False
          have "connected' ?G ?C"
            unfolding fukakyo_less_def
          proof (rule lemma_7_aux_5, goal_cases)
            case 1
            show ?case
            proof (rule lemma_7_aux_5, goal_cases)
              case 1
              show ?case
              proof (rule connected'_1, goal_cases)
                case 1
                have "r \<notin> D a"
                  using a_mem_V False
                  by (auto simp add: mem_D_iff_tree_path dest: tree_path_if_mem_V no_closed_tree_path_2)
                thus ?case
                  using r_mem_V
                  by (auto simp add: undirect_P_eq_G[symmetric] dest: connected'_Diff_D)
              next
                case 2
                show ?case
                  using D_refl v
                  by (fastforce simp add: mem_D_iff_tree_path dest: tree_path_if_tree_arc' tree_path_trans)
              qed
            next
              case 2
              show ?case
              proof (standard, goal_cases)
                case (1 y)
                thus ?case
                proof (intro connected'_1, goal_cases)
                  case 1
                  hence "y \<in> Directed_Multigraph.V (edges_from_fun I)"
                    by (fast dest: mem_childrenD head_tree_arc'_mem_V)
                  thus ?case
                    by (auto simp add: undirect_P_eq_G dest: connected'_D)
                next
                  case 2
                  hence "a \<notin> D y"
                    by (fastforce simp add: mem_D_iff_tree_path dest: mem_childrenD no_closed_tree_path_3)
                  moreover have "b \<notin> D y"
                    using v(2-3) 2
                    by (fastforce simp add: mem_D_iff_tree_path dest: mem_childrenD disjoint_siblings)
                  ultimately show ?case
                    by blast
                qed
              qed
            next
              case 3
              show ?case
              proof (standard, goal_cases)
                case (1 y)
                have "lowpt1 y \<in> ?A"
                proof
                  show "lowpt1 y \<in> D r"
                    using 1
                    by
                      (auto
                        simp add: mem_D_iff_tree_path
                        dest: mem_childrenD head_tree_arc'_mem_V lowpt1_mem_V tree_path_if_mem_V)
                  show "lowpt1 y \<notin> D a"
                  proof -
                    have "N (lowpt1 y) < N a"
                      using False 1
                      by (blast dest: mem_childrenD lemma_5_2)
                    thus ?thesis
                      by (auto simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path)
                  qed
                qed
                moreover hence "tree_path_snoc_frond' y (lowpt1 y)"
                  using lowpt1 1
                  by (force simp add: mem_D_iff_tree_path dest: mem_childrenD tree_path_if_tree_arc')
                ultimately show ?case
                  by blast
              qed
            qed
          next
            case 2
            show ?case
            proof (standard, goal_cases)
              case (1 y)
              thus ?case
              proof (intro connected'_1, goal_cases)
                case 1
                hence "y \<in> Directed_Multigraph.V (edges_from_fun I)"
                  by (fast dest: mem_agublagu_less_imp_mem_children mem_childrenD head_tree_arc'_mem_V)
                thus ?case
                  by (auto simp add: undirect_P_eq_G dest: connected'_D)
              next
                case 2
                hence "b \<notin> D y"
                  by
                    (fastforce
                      simp add: mem_D_iff_tree_path
                      dest: mem_agublagu_less_imp_mem_children mem_childrenD no_closed_tree_path_3)
                moreover hence "a \<notin> D y"
                  using v(2, 3)
                  by (auto simp add: mem_D_iff_tree_path dest: tree_path_if_tree_arc' tree_path_trans)
                ultimately show ?case
                  by blast
              qed
            qed
          next
            case 3
            show ?case
            proof (standard, goal_cases)
              case (1 y)
              have lowpt1_y_mem_A: "lowpt1 y \<in> ?A"
              proof
                show "lowpt1 y \<in> D r"
                  using 1
                  by
                    (fastforce
                      simp add: mem_D_iff_tree_path
                      dest: mem_agublagu_less_imp_mem_children mem_childrenD head_tree_arc'_mem_V lowpt1_mem_V tree_path_if_mem_V)
                show "lowpt1 y \<notin> D a"
                proof -
                  have "N (lowpt1 y) < N a"
                    using 1
                    by (fast dest: mem_agublagu_lessD)
                  thus ?thesis
                    by (auto simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path)
                qed
              qed
              moreover have "tree_path_snoc_frond' y (lowpt1 y)"
              proof -
                have "y \<in> D a"
                  using v(2, 3) 1
                  by
                    (force
                      simp add: mem_D_iff_tree_path
                      dest: tree_path_if_tree_arc' mem_agublagu_less_imp_mem_children mem_childrenD tree_path_trans)
                thus ?thesis
                  using lowpt1 lowpt1_y_mem_A
                  by force
              qed
              ultimately show ?case
                by blast
            qed
          qed
          thus ?thesis
            by (blast intro: connected'_subset_connected_component that)
        qed
        obtain C2 where
          C2: "C2 \<in> connected_components ?G"
          "?Y \<subseteq> C2"
        proof (cases "v = b")
          case True
          hence "?Y = {}"
            using no_D_mem_connected_components v(2)
            by (intro lemma_7_aux_4)
          thus ?thesis
            using 1 False
            by (blast elim: separation_class_13 intro: that)
        next
          case False
          have "connected' ?G ?Y"
            unfolding fukakyo_geq_def
          proof (rule lemma_7_aux_5, goal_cases)
            case 1
            show ?case
            proof (rule connected'_1, goal_cases)
              case 1
              have "v \<notin> D b"
                using v(3) False
                by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path_2)
              thus ?case
                using v(1)
                by (auto simp add: undirect_P_eq_G[symmetric] dest: connected'_Diff_D)
            next
              case 2
              show ?case
                using v(2) D_refl
                by (fastforce simp add: mem_D_iff_tree_path dest: no_closed_tree_path_3)
            qed
          next
            case 2
            show ?case
            proof (standard, goal_cases)
              case (1 y)
              thus ?case
              proof (intro connected'_1, goal_cases)
                case 1
                hence "y \<in> Directed_Multigraph.V (edges_from_fun I)"
                  by (fast dest: mem_agublagu_geq_imp_mem_children mem_childrenD head_tree_arc'_mem_V)
                thus ?case
                  by (auto simp add: undirect_P_eq_G dest: connected'_D)
              next
                case 2
                hence "b \<notin> D y"
                  by
                    (fastforce
                      simp add: mem_D_iff_tree_path
                      dest: mem_agublagu_geq_imp_mem_children mem_childrenD no_closed_tree_path_3)
                moreover hence "a \<notin> D y"
                  using v(2, 3)
                  by (auto simp add: mem_D_iff_tree_path dest: tree_path_if_tree_arc' tree_path_trans)
                ultimately show ?case
                  by blast
              qed
            qed
          next
            case 3
            show ?case
              using v(2, 3) no_D_mem_connected_components
              by (blast elim: lemma_7_aux_2 intro: mem_agublagu_geq_imp_mem_children)
          qed
          thus ?thesis
            by (blast intro: connected'_subset_connected_component that)
        qed
        have C2_neq_C1: "C2 \<noteq> C1"
        proof
          assume assm: "C2 = C1"
          obtain C3 where
            C3: "C3 \<in> connected_components ?G"
            "C3 \<noteq> C1"
            using 1 False C1(1)
            by (elim separation_class_99)
          then obtain x where
            x: "x \<in> C3"
            "x \<notin> C1"
            using C1(1)
            by (blast dest: connected_component_non_empty_2 connected_components_disjoint)
          have "x \<in> Multigraph.V G - {a, b}"
            using V_idk_4_subset C3(1) x(1)
            by (fast dest: connected_component_subset_2)
          moreover have "x \<notin> ?C \<union> ?Y"
            using C1(2) C2(2) assm x(2)
            by blast
          ultimately show False
            by (auto simp add: V_cong)
        qed
        moreover have "C1 = ?C"
        proof -
          { fix x
            assume
              assm: "x \<in> C1"
              "x \<notin> ?C"
            have "x \<in> Multigraph.V G - {a, b}"
              using V_idk_4_subset C1(1) assm(1)
              by (fast dest: connected_component_subset_2)
            moreover have "x \<notin> ?Y"
              using C1(1) C2 C2_neq_C1 assm(1)
              by (fast dest: connected_components_disjoint)
            ultimately have False
              using assm(2)
              by (auto simp add: V_cong) }
          thus ?thesis
            using C1(2)
            by blast
        qed
        moreover have "C2 = ?Y"
        proof -
          { fix x
            assume
              assm: "x \<in> C2"
              "x \<notin> ?Y"
            have "x \<in> Multigraph.V G - {a, b}"
              using V_idk_4_subset C2(1) assm(1)
              by (fast dest: connected_component_subset_2)
            moreover have "x \<notin> ?C"
              using C1 C2(1) C2_neq_C1 assm(1)
              by (blast dest: connected_components_disjoint)
            ultimately have False
              using assm(2)
              by (auto simp add: V_cong) }
          thus ?thesis
            using C2(2)
            by blast
        qed
        ultimately show
          "?C \<in> connected_components ?G"
          "?Y \<in> connected_components ?G"
          "?Y \<noteq> ?C"
          using C1(1) C2(1)
          by fastforce+
      qed
      have "is_type_2_pair a b v"
      proof (rule is_type_2_pair_if)
        show a_neq_r: "a \<noteq> r"
        proof
          assume assm: "a = r"
          hence "?C = {}"
            using v(2)
            by (intro lemma_7_aux_3)
          thus False
            using C_mem_connected_components
            by (auto dest: connected_component_non_empty_2)
        qed
        show "a \<rightarrow> v"
          using v(2)
          .
        show v_neq_b: "v \<noteq> b"
        proof
          assume "v = b"
          hence "?Y = {}"
            using no_D_mem_connected_components v(2)
            by (intro lemma_7_aux_4)
          thus False
            using Y_mem_connected_components
            by (auto dest: connected_component_non_empty_2)
        qed
        let ?y = "lowpt1 v"
        have y_less_a: "N ?y < N a"
          using a_neq_r v(2)
          by (intro lemma_5_2)
        obtain x where
          x: "first_descendant v x"
          "frond' x ?y"
        proof -
          have "?y \<noteq> v"
            using v(2) y_less_a
            by (auto dest: N_less_if_tree_arc')
          thus ?thesis
            using v(1)
            by (auto elim: first_descendant_1 intro: that)
        qed
        show "first_descendant v b"
          using x(1) v(3)
        proof (rule first_descendant_pref)
          have "x \<in> fukakyo_less b (i\<^sub>0 a b) \<union> {b}"
          proof -
            have "x \<in> ?C \<union> {a, b}"
            proof -
              have "?y \<in> ?B"
              proof -
                have "?y \<in> ?A"
                proof (standard, goal_cases)
                  case 1
                  show ?case
                    using v(1)
                    by (auto simp add: D_r_eq_V intro: lowpt1_mem_V)
                next
                  case 2
                  show ?case
                    using y_less_a
                    by (auto simp add: mem_D_iff_tree_path dest: N_leq_if_tree_path)
                qed
                thus ?thesis
                  using v(2)
                  by (auto dest: tree_path_if_tree_arc' D_subsetI)
              qed
              thus ?thesis
                using C_mem_connected_components x(2)
                by (intro connected_component_1[of ?C G "{a, b}" ?y x]) (auto simp add: edge_iff_3)
            qed
            moreover have "x \<notin> ?B"
            proof (standard, goal_cases)
              case 1
              hence "x \<in> \<Union> (D ` (set (children a) - {v}))"
                using v(2) x(1)
                by (auto simp add: mem_D_iff_tree_path dest: tree_path_if_tree_arc' first_descendant_imp_tree_path tree_path_trans)
              then obtain a' where
                "a \<rightarrow> a'"
                "a' \<noteq> v"
                "x \<in> D a'"
                by (blast dest: mem_childrenD)
              moreover have "x \<in> D v"
                using x(1)
                by (auto simp add: mem_D_iff_tree_path dest: first_descendant_imp_tree_path)
              ultimately show ?case
                using v(2)
                by (blast dest: disjoint_siblings)
            qed
            moreover have "x \<noteq> a"
              using v(2) x(1)
              by (fastforce dest: first_descendant_imp_tree_path no_closed_tree_path_3)
            ultimately show ?thesis
              by blast
          qed
          thus "b \<rightarrow>\<^sup>* x"
            using D_fukakyo_cong
            by (fastforce simp add: mem_D_iff_tree_path)
        qed
        show "connected_component ?G v \<subseteq> ?Y"
        proof -
          have "v \<in> ?Y"
            using D_refl v(3) v_neq_b
            by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path_2)
          thus ?thesis
            using Y_mem_connected_components
            by (blast dest: connected_component_71)
        qed
      qed
      thus ?thesis
        by (auto simp add: is_type_2_pair'_def)
    qed
  qed
next
  let ?G = "idk_4 G {a, b}"
  case 2
  thus ?case
  proof (elim disjE, goal_cases)
    case 1
    then obtain s t where
      "b \<rightarrow> s"
      "D s \<in> connected_components ?G"
      "t \<in> Multigraph.V ?G"
      "t \<notin> D s"
      using assms
      by (auto simp add: is_type_1_pair'_def dest: is_type_1_pair_imp)
    thus ?case
      by
        (intro is_separation_pairI_10[where ?C1.0 = "D s" and ?C2.0 = "connected_component ?G t"])
        (auto simp add: connected_components_image_cong dest: connected_component_refl)
  next
    let ?C1 = "connected_component ?G r"
    case 2
    then obtain s where
      a_neq_r: "a \<noteq> r" and
      tree_arc'_a_s: "a \<rightarrow> s" and
      s_neq_b: "s \<noteq> b" and
      first_descendant_s_b: "first_descendant s b" and
      C2_subset_X: "connected_component ?G s \<subseteq> D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b)" (is "?C2 \<subseteq> ?X")
      using assms
      by (auto simp add: is_type_2_pair'_def dest: is_type_2_pair_imp)
    hence a_mem_V: "a \<in> Directed_Multigraph.V (edges_from_fun I)"
      by (intro tail_tree_arc'_mem_V)
    show ?case
    proof (rule is_separation_pairI_10[where ?C1.0 = ?C1 and ?C2.0 = ?C2])
      show
        "?C1 \<in> connected_components ?G"
        "?C2 \<noteq> ?C1"
      proof -
        have "r \<in> Multigraph.V ?G"
        proof -
          have "r \<in> Multigraph.V G"
            using r_mem_V
            by (simp add: undirect_P_eq_G[symmetric]_V_image_undirect_eq)
          moreover have "r \<noteq> a"
            using a_neq_r
            ..
          moreover have "r \<noteq> b"
            using a_mem_V assms
            by (fast dest: neq_rI)
          ultimately show ?thesis
            by (simp add: V_idk_4_eq)
        qed
        moreover have "r \<notin> ?X"
        proof (standard, goal_cases)
          case 1
          have "?X \<subseteq> D s"
            using D_fukakyo_cong first_descendant_s_b
            by (blast dest: D_subsetI first_descendant_imp_tree_path)
          hence "a \<rightarrow>\<^sup>+ r"
            using tree_arc'_a_s 1
            by (fastforce simp add: mem_D_iff_tree_path intro: non_empty_tree_pathI_2)
          thus ?case
            using a_mem_V
            by (blast dest: N_less_if_non_empty_tree_path neq_rI)
        qed
        ultimately show
          "?C1 \<in> connected_components ?G"
          "?C2 \<noteq> ?C1"
          using C2_subset_X
          by (auto simp add: connected_components_image_cong dest: connected_component_refl)
      qed
      show "?C2 \<in> connected_components ?G"
      proof -
        have "s \<in> Multigraph.V ?G"
        proof -
          have "s \<in> Multigraph.V G"
            using tree_arc'_a_s
            by (auto simp add: V_E_I_eq_V_G dest: head_tree_arc'_mem_V)
          moreover have "s \<noteq> a"
            using tree_arc'_a_s
            by (blast dest: no_loop)
          ultimately show ?thesis
            using s_neq_b
            by (simp add: V_idk_4_eq)
        qed
        thus ?thesis
          by (simp add: connected_components_image_cong)
      qed
    qed
  next
    case 3
    thus ?case
      by (intro is_separation_pairI_3) simp+
  qed
qed

end