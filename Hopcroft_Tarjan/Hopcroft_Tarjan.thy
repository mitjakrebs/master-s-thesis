section \<open>Hopcroft-Tarjan algorithm\<close>
theory Hopcroft_Tarjan
  imports
    "../Graph/Incidence_Structure/Directed_Incidence_Structure"
    "../Graph/Graph"
    "HOL-Data_Structures.Map_Specs"
    "../Graph/Incidence_Structure/Undirected_Incidence_Structure"
begin

subsection \<open>Finding separation pairs\<close>

definition to_edge :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge" where
  "to_edge v p \<equiv> (fst p, (v, snd p))"

definition incidence :: "('b \<Rightarrow> ('a \<times> 'b) list) \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list" where
  "incidence I v \<equiv> map (to_edge v) (I v)"

lemma tail_eq:
  assumes "e \<in> set (incidence I v)"
  shows "tail e = v"
  using assms
  by (auto simp add: incidence_def to_edge_def tail_def endpoints_def)

(* TODO: Rename. *)
definition E :: "('b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list) \<Rightarrow> ('a, 'b) Directed_Multigraph.multigraph" where
  "E I \<equiv> \<Union>v. set (I v)"

definition is_numbering :: "'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> bool" where
  "is_numbering S N \<equiv> bij_betw N S {1..card S}"

locale steps_1_2_3_high =
  fixes r :: 'b
  fixes T :: "'b \<rightharpoonup> 'a \<times> 'b"
  fixes N :: "'b \<Rightarrow> nat"
  fixes I :: "'b \<Rightarrow> ('a \<times> 'b) list"
  assumes palm_tree: "palm_tree r T (E (incidence I))"
  assumes is_numbering: "is_numbering (Directed_Multigraph.V (E (incidence I))) N"
begin
sublocale palm_tree r T "E (incidence I)"
  using palm_tree
  .
end

lemma (in steps_1_2_3_high) N_eq_iff:
  assumes "u \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  assumes "v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  shows "N u = N v \<longleftrightarrow> u = v"
  using is_numbering assms
  unfolding is_numbering_def
  by (metis bij_betw_iff_bijections)

lemma (in steps_1_2_3_high) N_geq_1:
  assumes "v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  shows "1 \<le> N v"
  using is_numbering assms
  by (auto simp add: is_numbering_def bij_betw_iff_bijections)

definition (in steps_1_2_3_high) A :: "'b \<Rightarrow> 'b list" where
  "A v \<equiv> map snd (I v)"

lemma (in steps_1_2_3_high) A_incidence_cong:
  shows "A v = map head (incidence I v)"
  by (simp add: A_def head_def endpoints_def incidence_def to_edge_def)

lemma (in steps_1_2_3_high) mem_A_if_tree_arc':
  assumes "u \<rightarrow> v"
  shows "v \<in> set (A u)"
  sorry
(*
  obtain \<epsilon> where
    "tree_arc T (\<epsilon>, u, v)"
    using assms
    by (elim tree_arc'E)
  hence "(\<epsilon>, u, v) \<in> E (incidence I)"
    using palm_tree
    by (fastforce dest: palm_treeD(1) is_tbd_treeD(3))
  hence "(\<epsilon>, u, v) \<in> set (incidence I u)"
    using tail_eq
    by (fastforce simp add: E_def tail_def endpoints_def)
  thus ?thesis
    by (force simp add: A_incidence_cong head_def endpoints_def)
qed
*)

definition (in steps_1_2_3_high) children :: "'b \<Rightarrow> 'b list" where
  "children v \<equiv> filter (tree_arc' v) (A v)"

lemma (in steps_1_2_3_high) mem_childrenD:
  assumes "v \<in> set (children u)"
  shows "u \<rightarrow> v"
  using assms
  by (simp add: children_def)

lemma (in steps_1_2_3_high) mem_childrenI:
  assumes "u \<rightarrow> v"
  shows "v \<in> set (children u)"
  using assms
  by (auto simp add: children_def dest: mem_A_if_tree_arc')

(* QUESTION: Do we need this lemma? *)
lemma (in steps_1_2_3_high) partition_of_D:
  shows "({{v}} \<union> D ` set (children v)) partitions D v"
  sorry

lemma (in steps_1_2_3_high) D_children_cong:
  shows "{v} \<union> \<Union> (D ` set (children v)) = D v"
  using partition_of_D
  by (simp add: is_partition_of_def)

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

definition (in steps_1_2_3_high) fukakyo_less :: "'b \<Rightarrow> nat \<Rightarrow> 'b set" where
  "fukakyo_less v i \<equiv> \<Union> (D ` set (agublagu_less v i))"

definition (in steps_1_2_3_high) fukakyo_geq :: "'b \<Rightarrow> nat \<Rightarrow> 'b set" where
  "fukakyo_geq v i \<equiv> \<Union> (D ` set (agublagu_geq v i))"

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
  assumes "v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  shows "lowpt1 v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  using lowpt1 assms
  by (force dest: last_tree_path_snoc_frond'_mem_V)

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

lemma (in steps_1_2_3_high) N_lowpt1_least:
  assumes "tree_path_snoc_frond' u v"
  shows "N (lowpt1 u) \<le> N v"
  using finite_1 assms
  by (auto simp add: lowpt1_def intro: arg_min_least)

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

(*
lemma (in steps_1_2_3_high) idk_10:
  assumes "v \<in> D u"
  assumes "v \<noteq> u"
  assumes "v \<notin> fukakyo_geq u (i\<^sub>0 a b)"
  shows "v \<in> fukakyo_less u (i\<^sub>0 a b)"
  using assms D_fukakyo_cong
  by blast
*)

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
    by (cases) (simp_all add: \<phi>_def)
next
  case 2
  show ?case
    using assms
    by (intro sorted_wrt_\<phi>_A sorted_wrt_filter)
qed

locale steps_1_2_3_high_2 = steps_1_2_3_high +
  assumes P1: "N r = 1"
  assumes P2: "v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I)) \<Longrightarrow> N (A v ! i) = N v + card (fukakyo_geq v (i + 1)) + 1"
    (* QUESTION: Is this going to cause issues with Sorted_Less.sorted (incidence v G)? *)
  assumes P3: "sorted_wrt (\<lambda>e e'. \<phi> (tail e) (head e) \<le> \<phi> (tail e') (head e')) (incidence I v)"

locale steps_1_2_3_high_3 =
  biconnected_multigraph
  where G = G +
    steps_1_2_3_high_2
  where T = T
  for G :: "('a, 'b) Multigraph.multigraph"
    and T :: "'b \<rightharpoonup> 'a \<times> 'b" +
  assumes palm_tree_of: "palm_tree_of r T other (Hopcroft_Tarjan.E (incidence I)) G"
begin
sublocale palm_tree_of r T other "Hopcroft_Tarjan.E (incidence I)" G
  using palm_tree_of
  .
end

lemma (in steps_1_2_3_high_3) V_E_I_eq_V_G:
  shows "Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I)) = Multigraph.V G"
  using V_image_undirect_eq[symmetric]
  unfolding undirect_P_eq_G[symmetric]
  .

lemma (in steps_1_2_3_high_2) N_less_if_tree_arc':
  assumes "u \<rightarrow> v"
  shows "N u < N v"
proof -
  obtain i where
    "i < length (A u)"
    "(A u) ! i = v"
    using assms
    by (fastforce simp add: in_set_conv_nth dest: mem_A_if_tree_arc')
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

lemma (in steps_1_2_3_high_2) mem_fukakyo_geq_1:
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
  then consider
    "b' \<rightarrow>\<^sup>* b''" |
    "b'' \<rightarrow>\<^sup>* b'"
    using assms(3)
    by (blast dest: unique_tree_path)
  hence "b'' = b'"
    using b''(1) assms(2)
    by (cases) (blast dest: unique_tree_path_2 no_closed_tree_path_2)+
  thus ?case
    using b''(3)
    by simp
next
  case 2
  thus ?case
    using assms(2, 3)
    by (intro mem_fukakyo_geqI)
qed

definition (in steps_1_2_3_high_2) is_type_1_pair where
  "is_type_1_pair a b s t \<equiv>
   b \<noteq> a \<and>
   s \<noteq> a \<and>
   b \<rightarrow> s \<and>
   lowpt1 s = a \<and>
   N b \<le> N (lowpt2 s) \<and>
   t \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I)) \<and>
   t \<noteq> a \<and>
   t \<noteq> b \<and>
   t \<notin> D s"

lemma (in steps_1_2_3_high_2) is_type_1_pairD:
  assumes "is_type_1_pair a b s t"
  shows
    "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "b \<noteq> a"
    "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "s \<noteq> a"
    "s \<noteq> b"
    "b \<rightarrow> s"
    "lowpt1 s = a"
    "N b \<le> N (lowpt2 s)"
    "t \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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
    "t \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "t \<noteq> a"
    "t \<noteq> b"
    "t \<notin> D s"
    using assms
    by (simp_all add: is_type_1_pair_def)
  thus
    "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "s \<noteq> b"
    by (auto dest: N_less_if_tree_arc' intro: lowpt1_mem_V tail_tree_arc'_mem_V head_tree_arc'_mem_V)
qed

lemma (in steps_1_2_3_high_2) is_type_1_pairI:
  assumes
    "b \<noteq> a"
    "s \<noteq> a"
    "b \<rightarrow> s"
    "lowpt1 s = a"
    "N b \<le> N (lowpt2 s)"
    "t \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "t \<noteq> a"
    "t \<noteq> b"
    "t \<notin> D s"
  shows "is_type_1_pair a b s t"
  using assms
  by (simp add: is_type_1_pair_def)

definition (in steps_1_2_3_high_2) is_type_1_pair' where
  "is_type_1_pair' a b \<equiv> \<exists>s t. is_type_1_pair a b s t"

lemma (in steps_1_2_3_high_2) is_type_1_pair'D:
  assumes "is_type_1_pair' a b"
  shows
    "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "b \<noteq> a"
  using assms
  by (auto simp add: is_type_1_pair'_def dest: is_type_1_pairD(1-3))

lemma (in steps_1_2_3_high_2) is_type_1_pair'E:
  assumes "is_type_1_pair' a b"
  obtains s t where
    "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "s \<noteq> a"
    "s \<noteq> b"
    "b \<rightarrow> s"
    "lowpt1 s = a"
    "N b \<le> N (lowpt2 s)"
    "t \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "t \<noteq> a"
    "t \<noteq> b"
    "t \<notin> D s"
  using assms
  by (auto simp add: is_type_1_pair'_def dest: is_type_1_pairD)

lemma (in steps_1_2_3_high_2) is_type_1_pair'I:
  assumes "b \<noteq> a"
  assumes "s \<noteq> a"
  assumes "b \<rightarrow> s"
  assumes "lowpt1 s = a"
  assumes "N b \<le> N (lowpt2 s)"
  assumes "t \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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

(* QUESTION: Should we use trancl instead of rtrancl? *)
definition (in steps_1_2_3_high) first_descendant :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "first_descendant u v \<equiv> (u, v) \<in> {(u, v). first_child u = Some v}\<^sup>*"

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

(* TODO: This requires is_tbd_tree. *)
lemma (in steps_1_2_3_high) first_descendant_pref:
  assumes "first_descendant u w"
  assumes "u \<rightarrow>\<^sup>* v"
  assumes "v \<rightarrow>\<^sup>* w"
  shows "first_descendant u v"
  using assms
  sorry

(* TODO: This probably requires obtaining the path from v to x. *)
lemma (in steps_1_2_3_high_2) first_descendant_1:
  assumes "lowpt1 v \<noteq> v"
  obtains x where
    "first_descendant v x"
    "frond' x (lowpt1 v)"
  sorry

definition (in steps_1_2_3_high_2) is_type_2_pair where
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
    "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "N a \<noteq> 1"
    "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')"
    "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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
    "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "s \<noteq> a"
    "s \<rightarrow>\<^sup>* b"
    by
      (force
        simp add: tree_path_non_empty_tree_path_cong
        dest: tail_tree_arc'_mem_V first_descendant_imp_tree_path last_non_empty_tree_path_mem_V head_tree_arc'_mem_V N_less_if_tree_arc')+
qed

lemma (in steps_1_2_3_high_2) is_type_2_pairI:
  assumes "N a \<noteq> 1"
  assumes "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')"
  assumes "s \<noteq> b"
  assumes "a \<rightarrow> s"
  assumes "first_descendant s b"
  assumes "\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y"
  shows "is_type_2_pair a b s"
  using assms
  by (simp add: is_type_2_pair_def)

definition (in steps_1_2_3_high_2) is_type_2_pair' where
  "is_type_2_pair' a b \<equiv> \<exists>s. is_type_2_pair a b s"

lemma (in steps_1_2_3_high_2) is_type_2_pair'D:
  assumes "is_type_2_pair' a b"
  shows
    "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "N a \<noteq> 1"
    "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')"
  using assms
  by (auto simp add: is_type_2_pair'_def dest: is_type_2_pairD(1-4))

lemma (in steps_1_2_3_high_2) is_type_2_pair'E:
  assumes "is_type_2_pair' a b"
  obtains s where
    "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "s \<noteq> a"
    "s \<noteq> b"
    "a \<rightarrow> s"
    "s \<rightarrow>\<^sup>* b"
    "first_descendant s b"
    "\<forall>x y. frond' x y \<and> N s \<le> N x \<and> N x < N b \<longrightarrow> N a \<le> N y"
  using assms
  by (auto simp add: is_type_2_pair'_def dest: is_type_2_pairD(5-))

lemma (in steps_1_2_3_high_2) is_type_2_pair'I:
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

lemma (in steps_1_2_3_high_2) lemma_5_1:
  shows "length (children r) \<le> 1"
  sorry

lemma (in steps_1_2_3_high_2) lemma_5_2:
  assumes "u \<noteq> r"
  assumes "u \<rightarrow> v"
  shows "N (lowpt1 v) < N u"
  sorry

lemma (in steps_1_2_3_high_2) lemma_5_3:
  assumes "r \<rightarrow> v"
  shows "lowpt1 v = r"
  sorry

lemma (in steps_1_2_3_high_2) lemma_6_i_1:
  assumes "v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  shows "D v = {x. N v \<le> N x \<and> N x < ND v}"
  sorry

lemma (in steps_1_2_3_high_2) lemma_6_i_2:
  assumes "u \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  assumes "first_descendant u v"
  shows "D u - D v = {x. N u \<le> N x \<and> N x < N v}"
  sorry

lemma (in steps_1_2_3_high_3) lemma_6_ii:
  assumes "is_separation_pair G a b"
  assumes "N a < N b"
  shows "a \<rightarrow>\<^sup>+ b"
  sorry

(* TODO: Move. *)
lemma (in steps_1_2_3_high_3) neq_rI:
  assumes "u \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  assumes "N u < N v"
  shows "v \<noteq> r"
  using assms P1
  by (fastforce dest: N_geq_1)

lemma (in steps_1_2_3_high_3) lowpt1_mem_V_E_D:
  assumes "v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  shows "lowpt1 v \<in> Multigraph.V (Multigraph.E G (D v))"
  sorry

lemma (in steps_1_2_3_high_3) lowpt2_mem_V_E_D:
  assumes "v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
  shows "lowpt2 v \<in> Multigraph.V (Multigraph.E G (D v))"
  sorry

(* TODO: Move. *)
lemma (in steps_1_2_3_high_3) idk_50:
  shows "Multigraph.V (Multigraph.E (undirect ` Hopcroft_Tarjan.E (incidence I)) (D v)) = D v \<union> {u. u \<rightarrow> v} \<union> {x. tree_path_snoc_frond' v x}"
  sorry

lemma (in steps_1_2_3_high_3) idk_52:
  assumes "u \<rightarrow> v"
  shows "Multigraph.V (Multigraph.E (undirect ` Hopcroft_Tarjan.E (incidence I)) (D v)) = D v \<union> {u} \<union> {x. tree_path_snoc_frond' v x}"
  sorry

(* TODO: Move. *)
lemma (in steps_1_2_3_high_3) idk_51:
  assumes "Multigraph.E (undirect ` Hopcroft_Tarjan.E (incidence I)) (D v) \<in> separation_classes G a b"
  shows "Multigraph.V (Multigraph.E (undirect ` Hopcroft_Tarjan.E (incidence I)) (D v)) = D v \<union> {a, b}"
  sorry

(* TODO: Move. *)
lemma
  assumes "length l \<le> 1"
  assumes "x \<in> set l"
  shows "l = [x]"
  using assms
  by (cases l) simp+

(* TODO: Move. *)
lemma (in steps_1_2_3_high_3) mem_V_EI_tree_arc_1:
  assumes "x \<in> X"
  assumes "x \<rightarrow> y"
  shows "y \<in> Multigraph.V (Multigraph.E (undirect ` Hopcroft_Tarjan.E (incidence I)) X)"
proof -
  obtain \<epsilon> where
    "(\<epsilon>, {x, y}) \<in> G"
    using palm_tree_of assms(2)
    by (auto elim: palm_tree_of_2)
  thus ?thesis
    using assms(1)
    by (auto simp add: Multigraph.V_def Multigraph.endpoints_def Multigraph.E_def undirect_P_eq_G)
qed

(* TODO: Move. *)
lemma (in steps_1_2_3_high_3) mem_V_EI_tree_arc_2:
  assumes "x \<in> X"
  assumes "y \<rightarrow> x"
  shows "y \<in> Multigraph.V (Multigraph.E (undirect ` Hopcroft_Tarjan.E (incidence I)) X)"
proof -
  obtain \<epsilon> where
    "(\<epsilon>, {x, y}) \<in> G"
    using palm_tree_of assms(2)
    by (auto elim: palm_tree_of_2)
  thus ?thesis
    using assms(1)
    by (auto simp add: Multigraph.V_def Multigraph.endpoints_def Multigraph.E_def undirect_P_eq_G)
qed

(* TODO: Move. *)
lemma (in steps_1_2_3_high_3) mem_V_EI_frond_1:
  assumes "x \<in> X"
  assumes "frond' x y"
  shows "y \<in> Multigraph.V (Multigraph.E (undirect ` Hopcroft_Tarjan.E (incidence I)) X)"
proof -
  obtain \<epsilon> where
    "(\<epsilon>, {x, y}) \<in> G"
    using palm_tree_of assms(2)
    by (auto elim: palm_tree_of_2)
  thus ?thesis
    using assms(1)
    by (auto simp add: Multigraph.V_def Multigraph.endpoints_def Multigraph.E_def undirect_P_eq_G)
qed

(* TODO: Move. *)
lemma (in steps_1_2_3_high_3) mem_V_EI_frond_2:
  assumes "x \<in> X"
  assumes "frond' y x"
  shows "y \<in> Multigraph.V (Multigraph.E (undirect ` Hopcroft_Tarjan.E (incidence I)) X)"
proof -
  obtain \<epsilon> where
    "(\<epsilon>, {x, y}) \<in> G"
    using palm_tree_of assms(2)
    by (auto elim: palm_tree_of_2)
  thus ?thesis
    using assms(1)
    by (auto simp add: Multigraph.V_def Multigraph.endpoints_def Multigraph.E_def undirect_P_eq_G)
qed

lemma (in steps_1_2_3_high_3) idk_101:
  assumes "b \<rightarrow> b'"
  assumes "D b' \<notin> connected_components (idk_4 G {a, b})"
  obtains v where
    "v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "v \<noteq> a"
    "v \<noteq> b"
    "v \<notin> D b'"
    "tree_path_snoc_frond' b' v"
  sorry

lemma (in steps_1_2_3_high_3) lemma_7_aux:
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
    by (auto dest: unique_tree_path_2)
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
  obtain x where
    x: "x \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "x \<noteq> a"
    "x \<noteq> b"
    "x \<notin> D b'"
    "tree_path_snoc_frond' b' x"
    using assms(3-4)
    by (fastforce dest: mem_agublagu_geq_imp_mem_children mem_childrenD elim: idk_101)
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
      by (blast dest: mem_agublagu_geq_imp_mem_children mem_childrenD unique_tree_path_2)
    thus ?thesis
    proof (cases)
      case 1
      thus ?thesis
        using x(3)
        by (intro no_closed_tree_path)
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

lemma (in steps_1_2_3_high_3) is_type_1_pair_if:
  assumes non_empty_tree_path_a_b: "a \<rightarrow>\<^sup>+ b"
  assumes tree_arc'_b_s: "b \<rightarrow> s"
  assumes D_s_mem_connected_components: "D s \<in> connected_components (idk_4 G {a, b})"
  assumes t_mem_V: "t \<in> Multigraph.V (idk_4 G {a, b})"
  assumes t_not_mem_D_s: "t \<notin> D s"
  shows "is_type_1_pair a b s t"
proof (rule is_type_1_pairI)
  have
    a_mem_V: "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))" and
    b_mem_V: "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))" and
    a_less_b: "N a < N b"
    using non_empty_tree_path_a_b
    by (blast dest: hd_non_empty_tree_path_mem_V last_non_empty_tree_path_mem_V N_less_if_non_empty_tree_path)+
  have
    s_mem_V: "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))" and
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
      using s_mem_V D_s_mem_connected_components
      by (fast dest: lowpt1_mem_V_E_D connected_component_10)
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
      using s_mem_V D_s_mem_connected_components
      by (fast dest: lowpt2_mem_V_E_D connected_component_10)
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
    "t \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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
    "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))" and
    b_neq_a: "b \<noteq> a" and
    s: "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "s \<noteq> a"
    "s \<noteq> b"
    "b \<rightarrow> s"
    "lowpt1 s = a"
    "N b \<le> N (lowpt2 s)" and
    "t \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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
    have "tree_path_snoc_frond' s a"
      using s(2, 5) lowpt1
      by force
    hence "a \<rightarrow>\<^sup>* s"
      (* TODO: Beautify. *)
      by (metis N_less_if_non_empty_tree_path lemma_5_2 lemma_5_3 non_empty_tree_pathI_2 not_less_iff_gr_or_eq s(4) s(5) tree_path_snoc_frond'_imp_tree_path)
    hence "a \<rightarrow>\<^sup>* b"
      using s(2, 4)
      by (blast dest: unique_tree_path_2)
    thus ?thesis
      using b_neq_a
      by (simp add: tree_path_non_empty_tree_path_cong)
  qed
  show "D s \<in> connected_components (idk_4 G {a, b})"
  proof -
    let ?G = "idk_4 G {a, b}"
    have "connected' ?G (D s)"
    proof (rule connected'_1, goal_cases)
      case 1
      show ?case
        using s(1)
        by (auto simp add: undirect_P_eq_G dest: connected'_D)
    next
      case 2
      have "b \<notin> D s"
        using s(4)
        by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path_2)
      moreover have "a \<notin> D s"
        using non_empty_tree_path_a_b s(4)
        by
          (auto
            simp add: mem_D_iff_tree_path
            dest: non_empty_tree_path_imp_tree_path non_empty_tree_pathI no_closed_tree_path_3)
      ultimately show ?case
        by fast
    qed
    then obtain x y where
      x: "x \<in> D s" and
      y: "y \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
      "y \<noteq> a"
      "y \<noteq> b"
      "y \<notin> D s" and
      x_y_mem_endpoints: "{x, y} \<in> Multigraph.endpoints ` ?G"
      (* XXX *)
      using 1
      sorry
      by (elim connected'_not_connected_componentE)
    have "y \<in> D s"
      unfolding mem_D_iff_tree_path
      using s(4) y(3)
    proof (rule lemma_7_aux)
      have "{x, y} \<in> Multigraph.endpoints ` Multigraph.E G (D s)"
        (* XXX *)
        sorry
        thm mem_endpoints_EI
        by (intro mem_endpoints_EI)
      hence "y \<in> Multigraph.V (Multigraph.E G (D s))"
        by (auto simp add: Multigraph.mem_endpoints_iff intro: mem_VI(2))
      hence "y \<in> D s \<union> {b} \<union> {v. tree_path_snoc_frond' s v}"
        using s(4)
        by (simp add: idk_52 undirect_P_eq_G[symmetric])
      thus "tree_path_snoc_frond' s y"
        using y connected_component_subset V_idk_4_subset
        by fast
      thus "N b \<le> N y"
        using s(5-6) y(2)
        by (fastforce dest: N_lowpt2_leq)
    qed
    thus ?thesis
      using y(4)
      by simp
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
    a_mem_V: "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))" and
    s_mem_V: "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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
            dest: first_descendant_imp_tree_path no_closed_tree_path)
      thus ?case
        using s_mem_V
        by (auto simp add: undirect_P_eq_G[symmetric] dest: connected'_Diff_D)
    next
      case 2
      show ?case
        using tree_arc'_a_s D_refl
        by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path_2)
    qed
    moreover have "s \<in> ?X"
      using D_refl s_neq_b first_descendant_s_b
      by
        (auto
          simp add: mem_D_iff_tree_path
          dest: first_descendant_imp_tree_path no_closed_tree_path)
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
          by (blast dest: no_closed_tree_path_2)
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
              using s_mem_V first_descendant_s_b assm(2, 3)
              by (simp add: lemma_6_i_2)
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

(*
lemma (in steps_1_2_3_high_3) is_type_2_pair_if:
  assumes a_neq_r: "a \<noteq> r"
  assumes tree_arc'_a_s: "a \<rightarrow> s"
  assumes s_neq_b: "s \<noteq> b"
  assumes first_descendant_s_b: "first_descendant s b"
  assumes Y_mem_connected_components: "D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b) \<in> connected_components (idk_4 G {a, b})"
  shows "is_type_2_pair a b s"
proof (rule is_type_2_pairI)
  let ?X = "D s - D b"
  let ?Y = "?X \<union> fukakyo_geq b (i\<^sub>0 a b)"
  have
    a_mem_V: "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))" and
    s_mem_V: "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    using tree_arc'_a_s
    by (fast dest: tail_tree_arc'_mem_V head_tree_arc'_mem_V)+
  thus "N a \<noteq> 1"
    using r_mem_V a_neq_r
    by (simp add: N_eq_iff[symmetric] P1)
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
          thus ?thesis
            using Y_mem_connected_components assm(1)
            by (auto simp add: edge_iff_3 dest: connected_component_1)
        qed
        moreover have "x \<notin> ?X"
          using assm(4-5)
          by (auto simp add: mem_D_iff_tree_path dest: tree_path_if_tree_arc' tree_path_trans)
        moreover have "x \<noteq> a"
          using assm(1-2)
          by (fastforce dest: frond'_imp_tree_path N_leq_if_tree_path)
        moreover have "x \<noteq> b"
          using assm(4-5)
          by (blast dest: no_closed_tree_path_2)
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
          have "x \<in> ?X"
            using s_mem_V first_descendant_s_b assm(2, 3)
            by (simp add: lemma_6_i_2)
          thus ?thesis
            using Y_mem_connected_components assm(1)
            by (auto simp add: edge_iff_3 dest: connected_component_1)
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
*)

(* QQQ *)
lemma (in steps_1_2_3_high_3) is_type_2_pair_imp:
  assumes "is_type_2_pair a b s"
  shows
    "a \<noteq> r"
    "a \<rightarrow> s"
    "s \<noteq> b"
    "first_descendant s b"
    "connected_component (idk_4 G {a, b}) s \<subseteq> D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b)"
  sorry
proof -
  let ?G = "idk_4 G {a, b}"
  let ?X = "D s - D b"
  let ?Y = "?X \<union> fukakyo_geq b (i\<^sub>0 a b)"
  have
    "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "N a \<noteq> 1"
    "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')" and
    s: "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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
  have "connected' ?G ?Y"
    sorry
  then obtain x y where
    x: "x \<in> ?Y" and
    y: "y \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "y \<noteq> a"
    "y \<noteq> b"
    "y \<notin> ?Y" and
    x_y_mem_endpoints: "{x, y} \<in> Multigraph.endpoints ` ?G"
    (* XXX *)
    using 1
    sorry
    by (elim connected'_not_connected_componentE)
  then consider
    (x_mem_X) "x \<in> ?X" |
    (x_mem_fukakyo_geq) "x \<in> fukakyo_geq b (i\<^sub>0 a b)"
    by blast
  thus "?Y \<in> connected_components ?G"
  proof (cases)
    (* QQQ *)
    case x_mem_X
    then show ?thesis sorry
  next
    case x_mem_fukakyo_geq
    then obtain b' where
      b': "b \<rightarrow> b'"
      "b' \<rightarrow>\<^sup>* x"
      "N a \<le> N (lowpt1 b')"
      using P3
      by (blast dest: sorted_wrt_lowpt1_children elim: mem_fukakyo_geqE)
    have tree_path_snoc_frond'_b'_y: "tree_path_snoc_frond' b' y"
      (* QQQ *)
      sorry
    hence tree_path_snoc_frond'_s_y: "tree_path_snoc_frond' s y"
      using s(5) b'(1)
      by (auto dest: tree_path_if_tree_arc' tree_path_snoc_frond'I_2)
    hence tree_path_snoc_frond'_a_y: "tree_path_snoc_frond' a y"
      using s(4)
      by (auto dest: tree_path_if_tree_arc' tree_path_snoc_frond'I_2)

    have "y \<in> ?Y"
    proof -
      have "y \<in> D s"
        unfolding mem_D_iff_tree_path
        using s(4) y(2) tree_path_snoc_frond'_s_y
      proof (rule lemma_7_aux, goal_cases)
        case 1
        show ?case
          using tree_path_snoc_frond'_b'_y b'(3)
          by (fastforce dest: N_lowpt1_least)
      qed
      moreover
      { assume assm: "y \<in> D b"
        have "y \<in> D b'"
          unfolding mem_D_iff_tree_path
          using b'(1) y(3) tree_path_snoc_frond'_b'_y
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
      using y(4)
      by blast
  qed
qed

(*
lemma (in steps_1_2_3_high_3) is_type_2_pair_imp:
  assumes "is_type_2_pair a b s"
  shows
    "a \<noteq> r"
    "a \<rightarrow> s"
    "s \<noteq> b"
    "first_descendant s b"
    "D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b) \<in> connected_components (idk_4 G {a, b})"
proof -
  let ?G = "idk_4 G {a, b}"
  let ?X = "D s - D b"
  let ?Y = "?X \<union> fukakyo_geq b (i\<^sub>0 a b)"
  have
    "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "N a \<noteq> 1"
    "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "\<forall>b' x y. frond' x y \<and> N a < N y \<and> N y < N b \<and> b \<rightarrow> b' \<and> b' \<rightarrow>\<^sup>* x \<longrightarrow> N a \<le> N (lowpt1 b')" and
    s: "s \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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
  have "connected' ?G ?Y"
    sorry
  then obtain x y where
    x: "x \<in> ?Y" and
    y: "y \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
    "y \<noteq> a"
    "y \<noteq> b"
    "y \<notin> ?Y" and
    x_y_mem_endpoints: "{x, y} \<in> Multigraph.endpoints ` ?G"
    (* XXX *)
    using 1
    sorry
    by (elim connected'_not_connected_componentE)
  then consider
    (x_mem_X) "x \<in> ?X" |
    (x_mem_fukakyo_geq) "x \<in> fukakyo_geq b (i\<^sub>0 a b)"
    by blast
  thus "?Y \<in> connected_components ?G"
  proof (cases)
    (* QQQ *)
    case x_mem_X
    then show ?thesis sorry
  next
    case x_mem_fukakyo_geq
    then obtain b' where
      b': "b \<rightarrow> b'"
      "b' \<rightarrow>\<^sup>* x"
      "N a \<le> N (lowpt1 b')"
      using P3
      by (blast dest: sorted_wrt_lowpt1_children elim: mem_fukakyo_geqE)
    have tree_path_snoc_frond'_b'_y: "tree_path_snoc_frond' b' y"
      (* QQQ *)
      sorry
    hence tree_path_snoc_frond'_s_y: "tree_path_snoc_frond' s y"
      using s(5) b'(1)
      by (auto dest: tree_path_if_tree_arc' tree_path_snoc_frond'I_2)
    hence tree_path_snoc_frond'_a_y: "tree_path_snoc_frond' a y"
      using s(4)
      by (auto dest: tree_path_if_tree_arc' tree_path_snoc_frond'I_2)

    have "y \<in> ?Y"
    proof -
      have "y \<in> D s"
        unfolding mem_D_iff_tree_path
        using s(4) y(2) tree_path_snoc_frond'_s_y
      proof (rule lemma_7_aux, goal_cases)
        case 1
        show ?case
          using tree_path_snoc_frond'_b'_y b'(3)
          by (fastforce dest: N_lowpt1_least)
      qed
      moreover
      { assume assm: "y \<in> D b"
        have "y \<in> D b'"
          unfolding mem_D_iff_tree_path
          using b'(1) y(3) tree_path_snoc_frond'_b'_y
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
      using y(4)
      by blast
  qed
qed
*)

lemma (in steps_1_2_3_high_3) is_type_2_pair_iff:
  shows
    "is_type_2_pair a b s \<longleftrightarrow>
     a \<noteq> r \<and>
     a \<rightarrow> s \<and>
     s \<noteq> b \<and>
     first_descendant s b \<and>
     connected_component (idk_4 G {a, b}) s \<subseteq> D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b)"
  by (blast dest: is_type_2_pair_imp is_type_2_pair_if)

(*
lemma (in steps_1_2_3_high_3) is_type_2_pair_iff:
  shows
    "is_type_2_pair a b s \<longleftrightarrow>
     a \<noteq> r \<and>
     a \<rightarrow> s \<and>
     s \<noteq> b \<and>
     first_descendant s b \<and>
     D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b) \<in> connected_components (idk_4 G {a, b})"
  by (blast dest: is_type_2_pair_imp is_type_2_pair_if)
*)

lemma (in steps_1_2_3_high_3) lemma_7_aux_3:
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
      "lowpt1 b' \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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
    a_mem_V: "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))" and
    b_mem_V: "b \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
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
        using 1 assms
        by (auto simp add: is_type_1_pair'_def dest: lemma_6_ii intro: is_type_1_pair_if)
    next
      case no_D_mem_connected_components: False
      obtain v where
        v: "v \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
        "a \<rightarrow> v"
        "v \<rightarrow>\<^sup>* b"
        using 1 assms
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
          by (blast dest: spanning D_subsetI)
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
                  by (auto simp add: mem_D_iff_tree_path dest: spanning no_closed_tree_path)
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
                  hence "y \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
                    by (fast dest: mem_childrenD head_tree_arc'_mem_V)
                  thus ?case
                    by (auto simp add: undirect_P_eq_G dest: connected'_D)
                next
                  case 2
                  hence "a \<notin> D y"
                    by (fastforce simp add: mem_D_iff_tree_path dest: mem_childrenD no_closed_tree_path_2)
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
                        dest: mem_childrenD head_tree_arc'_mem_V lowpt1_mem_V spanning)
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
                hence "y \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
                  by (fast dest: mem_agublagu_less_imp_mem_children mem_childrenD head_tree_arc'_mem_V)
                thus ?case
                  by (auto simp add: undirect_P_eq_G dest: connected'_D)
              next
                case 2
                hence "b \<notin> D y"
                  by
                    (fastforce
                      simp add: mem_D_iff_tree_path
                      dest: mem_agublagu_less_imp_mem_children mem_childrenD no_closed_tree_path_2)
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
                      dest: mem_agublagu_less_imp_mem_children mem_childrenD head_tree_arc'_mem_V lowpt1_mem_V spanning)
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
                by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path)
              thus ?case
                using v(1)
                by (auto simp add: undirect_P_eq_G[symmetric] dest: connected'_Diff_D)
            next
              case 2
              show ?case
                using v(2) D_refl
                by (fastforce simp add: mem_D_iff_tree_path dest: no_closed_tree_path_2)
            qed
          next
            case 2
            show ?case
            proof (standard, goal_cases)
              case (1 y)
              thus ?case
              proof (intro connected'_1, goal_cases)
                case 1
                hence "y \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
                  by (fast dest: mem_agublagu_geq_imp_mem_children mem_childrenD head_tree_arc'_mem_V)
                thus ?case
                  by (auto simp add: undirect_P_eq_G dest: connected'_D)
              next
                case 2
                hence "b \<notin> D y"
                  by
                    (fastforce
                      simp add: mem_D_iff_tree_path
                      dest: mem_agublagu_geq_imp_mem_children mem_childrenD no_closed_tree_path_2)
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
              by (fastforce dest: first_descendant_imp_tree_path no_closed_tree_path_2)
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
            by (auto simp add: mem_D_iff_tree_path dest: no_closed_tree_path)
          thus ?thesis
            using Y_mem_connected_components
            by (blast dest: connected_component_71)
        qed
          (*
        show "?Y \<in> connected_components ?G"
          using Y_mem_connected_components
          .
*)
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
    hence a_mem_V: "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
      by (intro tail_tree_arc'_mem_V)
    show ?case
      thm is_separation_pairI_10
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
    (*
    let ?A = "connected_component ?G r"
    case 2
    then obtain s where
      a_neq_r: "a \<noteq> r" and
      tree_arc'_a_s: "a \<rightarrow> s" and
      s_neq_b: "s \<noteq> b" and
      first_descendant_s_b: "first_descendant s b" and
      X_mem_connected_components: "D s - D b \<union> fukakyo_geq b (i\<^sub>0 a b) \<in> connected_components ?G" (is "?X \<in> _")
      using assms
      by (auto simp add: is_type_2_pair'_def dest: is_type_2_pair_imp)
    hence a_mem_V: "a \<in> Directed_Multigraph.V (Hopcroft_Tarjan.E (incidence I))"
      by (intro tail_tree_arc'_mem_V)
    show ?case
      thm is_separation_pairI_10
      using X_mem_connected_components
    proof (rule is_separation_pairI_10[where ?C1.0 = ?X and ?C2.0 = ?A])
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
        "?A \<in> connected_components ?G"
        "?A \<noteq> ?X"
        by (auto simp add: connected_components_image_cong dest: connected_component_refl)
    qed
*)
  next
    case 3
    thus ?case
      by (intro is_separation_pairI_3) simp+
  qed
qed

subsection \<open>Specification of the algorithm\<close>

(* TODO: Rename. *)
datatype 'b T = EOS | Triple (h': nat) (a': 'b) (b': 'b)

type_synonym ('a, 'b) component = "('a, 'b) Directed_Multigraph.edge list"

record ('b, 't, 'g, 'm, 'a) state =
  root :: 'b
  tree :: 't
  multigraph :: 'g
  F :: 'm
  ESTACK :: "('a, 'b) Directed_Multigraph.edge list"
  TSTACK :: "'b T list"
  Cs :: "('a, 'b) component list"

(* QUESTION: Create locale Palm_Tree? *)
locale path_search =
  other
  where other = other +
    T: Map
  where empty = T_empty
    and update = T_update
    and delete = T_delete
    and lookup = T_lookup
    and invar = T_invar +
    P: Incidence_Structure
  where insert = insert +
    F: Map
  where empty = F_empty
    and update = F_update
    and delete = F_delete
    and lookup = F_lookup
    and invar = F_invar
  for other :: "('a::linorder, 'b::linorder) Multigraph.edge \<Rightarrow> 'b \<Rightarrow> 'b"
    and T_empty
    and T_update :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and T_delete
    and T_lookup
    and T_invar
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_empty
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm"
    and F_delete
    and F_lookup
    and F_invar +
  fixes while_loop_1 :: "('b, 't, 'g, 'm, 'a) state \<Rightarrow> ('b, 't, 'g, 'm, 'a) state"
  fixes while_loop_2 :: "('b, 't, 'g, 'm, 'a) state \<Rightarrow> ('b, 't, 'g, 'm, 'a) state"
  fixes while_loop_3 :: "('b, 't, 'g, 'm, 'a) state \<Rightarrow> ('b, 't, 'g, 'm, 'a) state"
  fixes while_loop_4 :: "('b, 't, 'g, 'm, 'a) state \<Rightarrow> ('b, 't, 'g, 'm, 'a) state"
  fixes algorithm_5 :: "('b, 't, 'g, 'm, 'a) state \<Rightarrow> ('b, 't, 'g, 'm, 'a) state"
  fixes algorithm_6 :: "('b, 't, 'g, 'm, 'a) state \<Rightarrow> ('b, 't, 'g, 'm, 'a) state"
  assumes root_while_loop_1: "root (while_loop_1 \<sigma>) = root \<sigma>"
  assumes root_while_loop_2: "root (while_loop_2 \<sigma>) = root \<sigma>"
  assumes root_while_loop_3: "root (while_loop_3 \<sigma>) = root \<sigma>"
  assumes root_while_loop_4: "root (while_loop_4 \<sigma>) = root \<sigma>"
  assumes root_algorithm_5: "root (algorithm_5 \<sigma>) = root \<sigma>"
  assumes root_algorithm_6: "root (algorithm_6 \<sigma>) = root \<sigma>"
begin

definition tree_arc :: "('a, 'b) Directed_Multigraph.edge \<Rightarrow> ('b, 't, 'g, 'm, 'a) state \<Rightarrow> bool" where
  "tree_arc e \<sigma> \<equiv> T_lookup (tree \<sigma>) (head e) = Some (fst e, tail e)"

definition traverse_tree_arc ::
  "('b \<Rightarrow> nat)
   \<Rightarrow> ('b \<Rightarrow> 'b)
      \<Rightarrow> ('b \<Rightarrow> 'b)
         \<Rightarrow> ('b \<Rightarrow> nat)
            \<Rightarrow> (('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool)
               \<Rightarrow> ('a, 'b) Directed_Multigraph.edge
                  \<Rightarrow> ('b, 't, 'g, 'm, 'a) state
                     \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "traverse_tree_arc N lowpt1 lowpt2 ND' START e \<sigma> \<equiv> \<sigma>"

definition traverse_frond ::
  "('b \<Rightarrow> nat)
   \<Rightarrow> ('b \<Rightarrow> 'b)
      \<Rightarrow> ('b \<Rightarrow> 'b)
         \<Rightarrow> ('b \<Rightarrow> nat)
            \<Rightarrow> (('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool)
               \<Rightarrow> ('a, 'b) Directed_Multigraph.edge
                  \<Rightarrow> ('b, 't, 'g, 'm, 'a) state
                     \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "traverse_frond N lowpt1 lowpt2 ND' START e \<sigma> \<equiv> \<sigma>"

(*
definition traverse_edge ::
  "('b \<Rightarrow> nat)
   \<Rightarrow> ('b \<Rightarrow> 'b)
      \<Rightarrow> ('b \<Rightarrow> 'b)
         \<Rightarrow> ('b \<Rightarrow> nat)
            \<Rightarrow> (('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool)
               \<Rightarrow> ('a, 'b) Directed_Multigraph.edge
                  \<Rightarrow> ('b, 't, 'g, 'm, 'a) state
                     \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "traverse_edge N lowpt1 lowpt2 ND' START e \<sigma> \<equiv>
   if tree_arc e \<sigma> then traverse_tree_arc N lowpt1 lowpt2 ND' START e \<sigma>
   else traverse_frond N lowpt1 lowpt2 ND' START e \<sigma>"
*)

(* QUESTION: Create locale Directed_Incidence_Structure and move? *)
definition incidence' :: "'g \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list" where
  "incidence' G v \<equiv> map (to_edge v) (incidence v G)"

(*
function (domintros) path_search and traverse_edge where
  "traverse_edge N lowpt1 lowpt2 ND' START e \<sigma> =
   (if tree_arc e \<sigma>
    then let \<sigma>1 = if START e then while_loop_1 \<sigma> else \<sigma>;
             \<sigma>2 = path_search N lowpt1 lowpt2 ND' START (head e) \<sigma>1;
             \<sigma>3 = \<sigma>2\<lparr>ESTACK := e # ESTACK \<sigma>2\<rparr>;
             \<sigma>4 = algorithm_5 \<sigma>3;
             \<sigma>5 = algorithm_6 \<sigma>4;
             \<sigma>6 = if START e then while_loop_2 \<sigma>5 else \<sigma>5;
             \<sigma>7 = while_loop_3 \<sigma>6
         in \<sigma>7
    else let \<sigma>8 = if START e then while_loop_4 \<sigma> else \<sigma>;
             \<sigma>9 = \<sigma>8\<lparr>ESTACK := e # ESTACK \<sigma>8\<rparr>
         in \<sigma>9)" |
  "path_search N lowpt1 lowpt2 ND' START v \<sigma> =
   fold (traverse_edge N lowpt1 lowpt2 ND' START) (incidence' (multigraph \<sigma>) v) \<sigma>"
  by pat_completeness simp+
thm path_search_traverse_edge.pinduct
*)

function (domintros) path_search ::
  "('b \<Rightarrow> nat)
   \<Rightarrow> ('b \<Rightarrow> 'b)
      \<Rightarrow> ('b \<Rightarrow> 'b)
         \<Rightarrow> ('b \<Rightarrow> nat)
            \<Rightarrow> (('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool)
               \<Rightarrow> 'b
                  \<Rightarrow> ('b, 't, 'g, 'm, 'a) state
                     \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "path_search N lowpt1 lowpt2 ND' START v \<sigma> =
   fold
    (\<lambda>e \<sigma>. if tree_arc e \<sigma>
           then let \<sigma>1 = if START e then while_loop_1 \<sigma> else \<sigma>;
                    \<sigma>2 = path_search N lowpt1 lowpt2 ND' START (head e) \<sigma>1;
                    \<sigma>3 = \<sigma>2\<lparr>ESTACK := e # ESTACK \<sigma>2\<rparr>;
                    \<sigma>4 = algorithm_5 \<sigma>3;
                    \<sigma>5 = algorithm_6 \<sigma>4;
                    \<sigma>6 = if START e then while_loop_2 \<sigma>5 else \<sigma>5;
                    \<sigma>7 = while_loop_3 \<sigma>6
                in \<sigma>7
           else let \<sigma>8 = if START e then while_loop_4 \<sigma> else \<sigma>;
                    \<sigma>9 = \<sigma>8\<lparr>ESTACK := e # ESTACK \<sigma>8\<rparr>
                in \<sigma>9)
    (incidence' (multigraph \<sigma>) v)
    \<sigma>"
  by auto
thm path_search.pinduct

definition traverse_edge where
  "traverse_edge N lowpt1 lowpt2 ND' START e \<sigma> \<equiv>
   if tree_arc e \<sigma>
   then let \<sigma>1 = if START e then while_loop_1 \<sigma> else \<sigma>;
            \<sigma>2 = path_search N lowpt1 lowpt2 ND' START (head e) \<sigma>1;
            \<sigma>3 = \<sigma>2\<lparr>ESTACK := e # ESTACK \<sigma>2\<rparr>;
            \<sigma>4 = algorithm_5 \<sigma>3;
            \<sigma>5 = algorithm_6 \<sigma>4;
            \<sigma>6 = if START e then while_loop_2 \<sigma>5 else \<sigma>5;
            \<sigma>7 = while_loop_3 \<sigma>6
        in \<sigma>7
   else let \<sigma>8 = if START e then while_loop_4 \<sigma> else \<sigma>;
            \<sigma>9 = \<sigma>8\<lparr>ESTACK := e # ESTACK \<sigma>8\<rparr>
        in \<sigma>9"

(*
definition path_search ::
  "('b \<Rightarrow> nat)
   \<Rightarrow> ('b \<Rightarrow> 'b)
      \<Rightarrow> ('b \<Rightarrow> 'b)
         \<Rightarrow> ('b \<Rightarrow> nat)
            \<Rightarrow> (('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool)
               \<Rightarrow> 'b
                  \<Rightarrow> ('b, 't, 'g, 'm, 'a) state
                     \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "path_search N lowpt1 lowpt2 ND' START v \<sigma> \<equiv>
   fold (traverse_edge N lowpt1 lowpt2 ND' START) (incidence' (multigraph \<sigma>) v) \<sigma>"
*)

end

locale algorithm_3_pre = path_search
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes F :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> 'm"
  fixes lowpt1 :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes lowpt2 :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> 'b \<Rightarrow> 'b"
  fixes ND :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> 'b \<Rightarrow> nat"
  fixes START :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> ('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool"
begin

definition init :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "init r T P \<equiv>
   \<lparr>root = r,
    tree = T,
    multigraph = P,
    F = F r T P,
    ESTACK = [],
    TSTACK = [EOS],
    Cs = []\<rparr>"

definition algorithm_3 :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) component list" where
  "algorithm_3 r T P N \<equiv>
   let \<sigma> = path_search N (lowpt1 r T P N) (lowpt2 r T P N) (ND r T P) (START r T P) r (init r T P)
   in ESTACK \<sigma> # Cs \<sigma>"

(*
definition algorithm_3 :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) component list" where
  "algorithm_3 r T P N \<equiv>
   ESTACK (path_search N (lowpt1 r T P N) (lowpt2 r T P N) (ND r T P) (START r T P) r (init r T P)) #
   Cs (path_search N (lowpt1 r T P N) (lowpt2 r T P N) (ND r T P) (START r T P) r (init r T P))"
*)

end

(* QUESTION: Create locale Undirected_Incidence_Structure? *)
locale algorithm_3 = algorithm_3_pre
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes T :: "'g \<Rightarrow> 'b \<Rightarrow> 't"
  fixes N :: "'g \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> nat"
  fixes I :: "'g \<Rightarrow> 'b \<Rightarrow> 'g"
  assumes steps_1_2_3_high_3:
    "\<lbrakk> biconnected_multigraph other (P.E G); r \<in> Multigraph.V (P.E G) \<rbrakk> \<Longrightarrow>
     steps_1_2_3_high_3 other r (N G r) (\<lambda>v. incidence v (I G r)) (P.E G) (T_lookup (T G r))"
begin

definition algorithm_3' :: "'g \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Multigraph.edge list list" where
  "algorithm_3' G r \<equiv> map (map undirect) (algorithm_3 r (T G r) (I G r) (N G r))"

end

subsection \<open>Verification of the correctness of the algorithm\<close>

subsubsection \<open>Assumptions on the input\<close>

locale path_search_valid_input = path_search
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes N :: "'b \<Rightarrow> nat"
  fixes lowpt1 :: "'b \<Rightarrow> 'b"
  fixes lowpt2 :: "'b \<Rightarrow> 'b"
  fixes ND' :: "'b \<Rightarrow> nat"
  fixes START :: "('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool"
  fixes v :: 'b
begin

abbreviation path_search' :: "('b, 't, 'g, 'm, 'a) state \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "path_search' \<equiv> path_search N lowpt1 lowpt2 ND' START v"

definition traverse_edge' where
  "traverse_edge' \<equiv> traverse_edge N lowpt1 lowpt2 ND' START"

(* declare path_search'_def [simp] *)

end

locale algorithm_3_pre_valid_input = algorithm_3_pre
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes r :: 'b
  fixes T :: 't
  fixes P :: 'g
  fixes N :: "'b \<Rightarrow> nat"
  assumes steps_1_2_3_high_2: "steps_1_2_3_high_2 r (T_lookup T) N (\<lambda>v. incidence v P)"
begin

sublocale steps_1_2_3_high_2
  where T = "T_lookup T"
    and I = "\<lambda>v. incidence v P"
  using steps_1_2_3_high_2
  .

(*
sublocale path_search_valid_input
  where lowpt1 = "lowpt1 r T P N"
    and lowpt2 = "lowpt2 r T P N"
    and ND' = "ND r T P"
    and START = "START r T P"
  ..
*)

end

definition (in algorithm_3_pre) algorithm_3_pre_valid_input' :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> bool" where
  "algorithm_3_pre_valid_input' \<equiv>
   algorithm_3_pre_valid_input
    empty delete incidence invar
    other
    T_empty T_delete T_lookup T_invar
    F_empty F_delete F_lookup F_invar
    while_loop_1
    while_loop_2
    while_loop_3
    while_loop_4
    algorithm_5
    algorithm_6
    T_update
    insert
    F_update"

locale algorithm_3_valid_input = algorithm_3
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes G :: 'g
  fixes r :: 'b
  assumes biconnected_multigraph: "biconnected_multigraph other (P.E G)"
  assumes r_mem_V: "r \<in> Multigraph.V (P.E G)"
begin

(* TODO: Rename. *)
sublocale steps_1_2_3_high_3
  where N = "N G r"
    and I = "\<lambda>v. incidence v (I G r)"
    and G = "P.E G"
    and T = "T_lookup (T G r)"
  using biconnected_multigraph r_mem_V
  by (intro steps_1_2_3_high_3)

(* TODO: Rename. *)
sublocale algorithm_3_pre_valid_input
  where T = "T G r"
    and P = "I G r"
    and N = "N G r"
  using algorithm_3_pre_axioms steps_1_2_3_high_2_axioms
  by
    (fastforce
      simp add: algorithm_3_pre_valid_input_axioms_def
      intro: algorithm_3_pre_valid_input.intro)

end

lemma (in path_search) incidence_eq_incidence':
  shows "Hopcroft_Tarjan.incidence (\<lambda>v. incidence v (I G r)) = incidence' (I G r)"
  by (auto simp add: incidence_def incidence'_def)

(* TODO: Move. *)
lemma (in path_search) E_incidence'_eq_A:
  shows "E (incidence' P) = P.A P"
  by (force simp add: E_def incidence'_def to_edge_def P.A_def)

(* TODO: Move. *)
lemma (in algorithm_3_valid_input) image_undirect_A_eq_E:
  shows "undirect ` P.A (I G r) = P.E G"
  using palm_tree_of
  by (force simp add: incidence_eq_incidence' E_incidence'_eq_A dest: palm_tree_ofD(2))

(* TODO: Move. *)
function (domintros) flatten :: "('b \<rightharpoonup> 'a \<times> 'b) \<Rightarrow> ('b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list) \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list" where
  "flatten T I u =
   fold
    (\<lambda>e. (@) (e # (if tree_arc T e then flatten T I (head e) else [])))
    (I u)
    []"
  by auto

(* TODO: Move. *)
definition agublagu :: "('b \<rightharpoonup> 'a \<times> 'b) \<Rightarrow> ('b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list) \<Rightarrow> 'b \<Rightarrow> 'b \<rightharpoonup> 'a \<times> 'b" where
  "agublagu T I u v \<equiv> if u \<rightarrow>\<^sup>+ v then T v else None"

lemma agublagu_eq_restrict_map:
  shows "agublagu T I u = T |` {v. u \<rightarrow>\<^sup>+ v}"
  by (auto simp add: agublagu_def restrict_map_def)

(* TODO: Move. *)
definition agublagu_2 :: "('b \<rightharpoonup> 'a \<times> 'b) \<Rightarrow> ('b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list" where
  "agublagu_2 T I u v \<equiv> if u \<rightarrow>\<^sup>* v then I v else []"

definition restrict_fun :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b list" where
  "restrict_fun f A \<equiv> (\<lambda>x. if x \<in> A then f x else [])"

lemma restrict_fun_eq_override_on:
  shows "restrict_fun f A = override_on (\<lambda>_. []) f A"
  by (simp add: restrict_fun_def override_on_def)

lemma agublagu_2_eq_restrict_fun:
  shows "agublagu_2 T I u = restrict_fun I (D u)"
  by (auto simp add: agublagu_2_def restrict_fun_def D_def)

lemma flatten_pinduct:
  assumes "flatten_dom (T, I, u)"
  assumes "\<And>T I u. (\<And>e. e \<in> set (I u) \<Longrightarrow> tree_arc T e \<Longrightarrow> Q T I (head e)) \<Longrightarrow> Q T I u"
  shows "Q T I u"
  using assms
  by (rule flatten.pinduct)

thm flatten.psimps
(* TODO: This lemma needs to be proven in a locale that relates T and I. *)
lemma
  assumes "flatten_dom (T, I, u)"
  shows "set (flatten T I u) = E (agublagu_2 T I u)"
proof (induct "I u")
  case Nil
  then show ?case sorry
next
  case (Cons a x)
  then show ?case sorry
qed

(*
function (in path_search) (domintros) flatten_aux :: "'t \<Rightarrow> 'g \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list" where
  "flatten_aux T P u =
   fold
    (\<lambda>(\<epsilon>, v). (@) ((\<epsilon>, u, v) # (if T_lookup T v = Some (\<epsilon>, u) then flatten_aux T P v else [])))
    (incidence u P)
    []"
  by auto

definition (in path_search) flatten :: "'t \<Rightarrow> 'g \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list" where
  "flatten \<equiv> flatten_aux"

function (in path_search) (domintros) agublagu_aux :: "'t \<Rightarrow> 'g \<Rightarrow> 'b \<Rightarrow> 't \<Rightarrow> 't" where
  "agublagu_aux T P u =
   fold
    (\<lambda>(\<epsilon>, v). if T_lookup T v = Some (\<epsilon>, u) then (T_update v (\<epsilon>, u)) \<circ> (agublagu_aux T P v) else id)
    (incidence u P)"
  by auto

definition (in path_search) agublagu :: "'t \<Rightarrow> 'g \<Rightarrow> 'b \<Rightarrow> 't" where
  "agublagu T P v \<equiv> agublagu_aux T P v T_empty"

function (in path_search) (domintros) agublagu_2_aux :: "'t \<Rightarrow> 'g \<Rightarrow> 'b \<Rightarrow> 'g \<Rightarrow> 'g" where
  "agublagu_2_aux T P u =
   fold
    (\<lambda>(\<epsilon>, v). (insert u (\<epsilon>, v) \<circ> (if T_lookup T v = Some (\<epsilon>, u) then agublagu_2_aux T P v else id)))
    (incidence u P)"
  by auto

definition (in path_search) agublagu_2 :: "'t \<Rightarrow> 'g \<Rightarrow> 'b \<Rightarrow> 'g" where
  "agublagu_2 T P v \<equiv> agublagu_2_aux T P v empty"
*)

subsubsection \<open>Loop invariants\<close>

locale path_search_invar = path_search_valid_input
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes \<sigma> :: "('b, 't, 'g, 'm, 'a) state"
    (* QUESTION: Use P.E instead? *)
  assumes finite_multigraph: "finite (undirect ` P.A (multigraph \<sigma>))"
  assumes finite_Cs: "Ball (set (map set (map (map undirect) (Cs \<sigma>)))) finite"
  assumes no_separation_pair_Cs: "\<forall>G\<in>set (map set (map (map undirect) (Cs \<sigma>))). \<not> (\<exists>a b. is_separation_pair G a b)"
    (* TODO: Order. *)
  assumes palm_tree: "palm_tree (root \<sigma>) (T_lookup (tree \<sigma>)) (E (incidence' (multigraph \<sigma>)))"
begin

abbreviation \<sigma>' :: "('b, 't, 'g, 'm, 'a) state" where
  "\<sigma>' \<equiv> path_search' \<sigma>"

(* declare \<sigma>'_def [simp] *)

end

(* QUESTION: Should this locale extend path_search_valid_input instead? *)
(* QUESTION: Do we need to fix another state? *)
locale traverse_edge_invar = path_search_invar
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes e
  assumes e_mem_set_incidence': "e \<in> set (incidence' (multigraph \<sigma>) v)"

locale traverse_edge_invar_tree_arc = traverse_edge_invar
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes tree_arc: "tree_arc e \<sigma>"

locale traverse_edge_invar_frond = traverse_edge_invar
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes frond: "\<not> tree_arc e \<sigma>"

abbreviation (in path_search) path_search_invar' ::
  "('b \<Rightarrow> nat)
   \<Rightarrow> ('b \<Rightarrow> 'b)
      \<Rightarrow> ('b \<Rightarrow> 'b)
         \<Rightarrow> ('b \<Rightarrow> nat)
            \<Rightarrow> (('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool)
               \<Rightarrow> 'b
                  \<Rightarrow> ('b, 't, 'g, 'm, 'a) state
                     \<Rightarrow> bool" where
  "path_search_invar' N lowpt1 lowpt2 ND' START v \<equiv>
   path_search_invar empty
    delete incidence invar
    other
    T_empty T_delete T_lookup T_invar
    F_empty F_delete F_lookup F_invar
    while_loop_1
    while_loop_2
    while_loop_3
    while_loop_4
    algorithm_5
    algorithm_6
    T_update
    insert
    F_update"

abbreviation (in path_search_valid_input) path_search_invar'' where
  "path_search_invar'' \<equiv> path_search_invar' N lowpt1 lowpt2 ND' START v"

context algorithm_3_pre_valid_input
begin
sublocale path_search_invar
  where lowpt1 = "lowpt1 r T P N"
    and lowpt2 = "lowpt2 r T P N"
    and ND' = "ND r T P"
    and START = "START r T P"
    and v = r
    and \<sigma> = "init r T P"
proof (standard, goal_cases)
  case 1
  then show ?case sorry
next
  case 2
  then show ?case sorry
next
  case 3
  then show ?case sorry
next
  case 4
  then show ?case sorry
qed
end

lemma (in path_search_invar) finite_multigraph_multigraph:
  shows "Multigraph.finite_multigraph other (undirect ` P.A (multigraph \<sigma>))"
  using finite_multigraph
  sorry

lemma (in path_search_invar) finite_multigraph_Cs:
  shows "Ball (set (map set (map (map undirect) (Cs \<sigma>)))) (Multigraph.finite_multigraph other)"
  sorry

(* QUESTION: Move to more general locale? *)
lemma (in path_search_invar) path_search_invar_mem_V:
  shows
    "is_split_tbd
      (undirect ` P.A (multigraph \<sigma>) # map set (map (map undirect) (Cs \<sigma>)))
      (undirect ` P.A (multigraph \<sigma>') # map set (map (map undirect) (Cs \<sigma>')))"
  sorry

(* QUESTION: Move to more general locale? *)
lemma (in path_search_invar) path_search_invar_2:
  shows "ESTACK \<sigma>' = flatten (T_lookup (tree \<sigma>')) (incidence' (multigraph \<sigma>')) v @ ESTACK \<sigma>"
  sorry

(* QUESTION: Move to more general locale? *)
(*
lemma (in path_search_invar) root_path_search:
  shows "root \<sigma>' = root \<sigma>"
  sorry
*)

(* QUESTION: Move to more general locale? *)
(* QUESTION: Is there a more concise conclusion? *)
lemma (in path_search_invar) path_search_invar_4:
  assumes "is_separation_pair (undirect ` P.A (multigraph \<sigma>')) a b"
  shows "a \<notin> D (T_lookup (tree \<sigma>')) v \<or> b \<notin> D (T_lookup (tree \<sigma>')) v"
  sorry

(* FIXME: *)
(*
lemma (in path_search_invar) path_search_invar_\<sigma>':
  shows "path_search_invar'' \<sigma>'"
  sorry
*)

subsubsection \<open>Termination\<close>

lemma (in path_search_valid_input) path_search_dom:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_dom (N, lowpt1, lowpt2, ND', START, v, \<sigma>)"
  sorry

lemma (in path_search_invar) path_search_dom:
  shows "path_search_dom (N, lowpt1, lowpt2, ND', START, v, \<sigma>)"
  using path_search_invar_axioms
  by (intro path_search_dom)

lemma (in path_search) path_search_simps:
  assumes "path_search_invar' N lowpt1 lowpt2 ND' START v \<sigma>"
  shows
    "path_search N lowpt1 lowpt2 ND' START v \<sigma> =
     fold (traverse_edge N lowpt1 lowpt2 ND' START) (incidence' (multigraph \<sigma>) v) \<sigma>"
  unfolding traverse_edge_def
  using assms
  by (intro path_search_invar.path_search_dom path_search.psimps)

lemma (in path_search_valid_input) path_search_traverse_edge_dom_Inl:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_traverse_edge_dom (Inl (N, lowpt1, lowpt2, ND', START, v, \<sigma>))"
  sorry

lemma (in path_search_valid_input) path_search_traverse_edge_dom_Inr:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_traverse_edge_dom (Inr (N, lowpt1, lowpt2, ND', START, e, \<sigma>))"
  sorry

lemma (in path_search_invar) path_search_traverse_edge_dom_Inl:
  shows "path_search_traverse_edge_dom (Inl (N, lowpt1, lowpt2, ND', START, v, \<sigma>))"
  sorry

lemma (in path_search_invar) path_search_traverse_edge_dom_Inr:
  shows "path_search_traverse_edge_dom (Inr (N, lowpt1, lowpt2, ND', START, e, \<sigma>))"
  sorry

(*
lemma (in path_search) path_search_traverse_edge_induct:
  assumes "path_search_invar' N lowpt1 lowpt2 ND' START v \<sigma>"
  assumes
    "\<And>N lowpt1 lowpt2 ND' START e \<sigma>.
        (tree_arc e \<sigma> \<Longrightarrow> P N lowpt1 lowpt2 ND' START (head e) (if START e then while_loop_1 \<sigma> else \<sigma>)) \<Longrightarrow>
        Q N lowpt1 lowpt2 ND' START e \<sigma>"
  assumes
    "\<And>N lowpt1 lowpt2 ND' START v \<sigma>.
        (\<And>e \<sigma>'. e \<in> set (incidence' (multigraph \<sigma>) v) \<Longrightarrow> Q N lowpt1 lowpt2 ND' START e \<sigma>') \<Longrightarrow>
        P N lowpt1 lowpt2 ND' START v \<sigma>"
  shows
    "P N lowpt1 lowpt2 ND' START v \<sigma>"
    "Q N lowpt1 lowpt2 ND' START e \<sigma>"
proof -
  show "P N lowpt1 lowpt2 ND' START v \<sigma>"
  proof (rule path_search_traverse_edge.pinduct[of N lowpt1 lowpt2 ND' START, where ?Q = Q], goal_cases)
    case 1
    then show ?case
      using assms(1)
      by (intro path_search_invar.path_search_traverse_edge_dom_Inl)
  next
    case (2 N lowpt1 lowpt2 ND' START e \<sigma>)
    thus ?case
      by (intro assms(2)) simp
  next
    case (3 N lowpt1 lowpt2 ND' START v \<sigma>)
    thus ?case
      by (intro assms(3))
  qed
  show "Q N lowpt1 lowpt2 ND' START e \<sigma>"
  proof (rule path_search_traverse_edge.pinduct[of N lowpt1 lowpt2 ND' START, where ?P = P], goal_cases)
    case 1
    then show ?case
      using assms(1)
      by (intro path_search_invar.path_search_traverse_edge_dom_Inr)
  next
    case (2 N lowpt1 lowpt2 ND' START e \<sigma>)
    thus ?case
      by (intro assms(2)) simp
  next
    case (3 N lowpt1 lowpt2 ND' START v \<sigma>)
    thus ?case
      by (intro assms(3))
  qed
qed
*)

lemma (in path_search) path_search_induct:
  assumes "path_search_invar' N lowpt1 lowpt2 ND' START v \<sigma>"
  assumes
    "\<And>N lowpt1 lowpt2 ND' START v \<sigma>.
        (\<And>e \<sigma>'.
            e \<in> set (incidence' (multigraph \<sigma>) v) \<Longrightarrow>
            tree_arc e \<sigma>' \<Longrightarrow>
            Q N lowpt1 lowpt2 ND' START (head e) (if START e then while_loop_1 \<sigma>' else \<sigma>')) \<Longrightarrow>
        Q N lowpt1 lowpt2 ND' START v \<sigma>"
  shows "Q N lowpt1 lowpt2 ND' START v \<sigma>"
    (* TODO: Remove of part. *)
proof (rule path_search.pinduct[of N lowpt1 lowpt2 ND' START v \<sigma>], goal_cases)
  case 1
  show ?case
    using assms(1)
    by (intro path_search_invar.path_search_dom)
next
  case (2 N lowpt1 lowpt2 ND' START v \<sigma>)
  thus ?case
    by (auto intro: assms(2))
qed

subsubsection \<open>Correctness\<close>

lemma a01:
  shows "set (flatten T I v) = E (agublagu_2 T I v)"
  sorry

lemma a02:
  assumes "is_tbd_tree r T (E  I)"
  shows "agublagu_2 T I r = I"
  sorry

(*
lemma (in path_search) root_path_search:
  assumes "path_search_invar' N lowpt1 lowpt2 ND' START v \<sigma>"
  shows
    "root (path_search N lowpt1 lowpt2 ND' START v \<sigma>) = root \<sigma>"
    "root (traverse_edge N lowpt1 lowpt2 ND' START e \<sigma>) = root \<sigma>"
  using assms
  thm path_search_traverse_edge_induct[OF assms, of _ _ N lowpt1 lowpt2 ND' START]
proof (induct rule: path_search_traverse_edge_induct[OF assms, of _ _ N lowpt1 lowpt2 ND' START])
  case (1 N lowpt1 lowpt2 ND' START e \<sigma>)
  then show ?case sorry
next
  case (2 N lowpt1 lowpt2 ND' START v \<sigma>)
  then show ?case sorry
qed
*)

lemma root_fold:
  assumes "\<And>e \<sigma>. e \<in> set l \<Longrightarrow> root (f e \<sigma>) = root \<sigma>"
  shows "root (fold f l \<sigma>) = root \<sigma>"
  using assms
proof (induct l arbitrary: \<sigma>)
  case Nil
  thus ?case
    by fastforce
next
  case (Cons e es)
  have "root (fold f (e # es) \<sigma>) = root (fold f es (f e \<sigma>))"
    by fastforce
  also have "... = root (f e \<sigma>)"
    using Cons.prems
    by (intro Cons.hyps) simp
  also have "... = root \<sigma>"
    by (intro Cons.prems) simp
  finally show ?case
    .
qed

lemma (in path_search) root_traverse_edge:
  assumes
    "tree_arc e \<sigma> \<Longrightarrow>
     root (path_search N lowpt1 lowpt2 ND' START (head e) (if START e then while_loop_1 \<sigma> else \<sigma>)) =
     root (if START e then while_loop_1 \<sigma> else \<sigma>)"
  shows "root (traverse_edge N lowpt1 lowpt2 ND' START e \<sigma>) = root \<sigma>"
proof (cases "tree_arc e \<sigma>")
  case True
  hence
    "root (traverse_edge N lowpt1 lowpt2 ND' START e \<sigma>) =
     root (path_search N lowpt1 lowpt2 ND' START (head e) (if START e then while_loop_1 \<sigma> else \<sigma>))"
    by (simp add: traverse_edge_def Let_def root_while_loop_3 root_while_loop_2 root_algorithm_6 root_algorithm_5)
  also have "... = root (if START e then while_loop_1 \<sigma> else \<sigma>)"
    using True
    by (intro assms)
  also have "... = root \<sigma>"
    by (simp add: root_while_loop_1)
  finally show ?thesis
    .
next
  case False
  thus ?thesis
    using root_while_loop_4
    by (simp add: traverse_edge_def Let_def)
qed

lemma (in path_search) root_path_search_aux:
  assumes "path_search_invar' N lowpt1 lowpt2 ND' START v \<sigma>"
  assumes "e \<in> set (incidence' (multigraph \<sigma>) v)"
  assumes "tree_arc e \<sigma>'"
  shows "path_search_invar' N lowpt1 lowpt2 ND' START v (if START e then while_loop_1 \<sigma>' else \<sigma>')"
  sorry

lemma (in path_search) root_path_search:
  assumes "path_search_invar' N lowpt1 lowpt2 ND' START v \<sigma>"
  shows "root (path_search N lowpt1 lowpt2 ND' START v \<sigma>) = root \<sigma>"
  using assms
proof (induct rule: path_search_induct[OF assms, of _ N lowpt1 lowpt2 ND' START v])
  case (1 N lowpt1 lowpt2 ND' START v \<sigma>)
  hence "root (fold (traverse_edge N lowpt1 lowpt2 ND' START) (incidence' (multigraph \<sigma>) v) \<sigma>) = root \<sigma>"
  proof -
    { fix e \<sigma>'
      assume "e \<in> set (incidence' (multigraph \<sigma>) v)"
      hence "root (traverse_edge N lowpt1 lowpt2 ND' START e \<sigma>') = root \<sigma>'"
        using "1.prems"
        by (auto intro: root_path_search_aux "1.hyps" root_traverse_edge) }
    thus ?thesis
      by (intro root_fold)
  qed
  thus ?case
    using "1.prems"
    by (simp add: path_search_simps)
qed

(*
lemma (in path_search) root_path_search:
  assumes "path_search_invar' N lowpt1 lowpt2 ND' START v \<sigma>"
  shows "root (path_search N lowpt1 lowpt2 ND' START v \<sigma>) = root \<sigma>"
  using assms
proof (induct rule: path_search_induct[OF assms, of _ N lowpt1 lowpt2 ND' START v])
  case (1 N lowpt1 lowpt2 ND' START v \<sigma>)
  hence "root (fold (traverse_edge N lowpt1 lowpt2 ND' START) (incidence' (multigraph \<sigma>) v) \<sigma>) = root \<sigma>"
  proof (induct "incidence' (multigraph \<sigma>) v" arbitrary: \<sigma>)
    case Nil
    thus ?case
      by simp
  next
    case (Cons e es)
    let ?\<sigma>' = "traverse_edge N lowpt1 lowpt2 ND' START e \<sigma>"
    have
      "root (fold (traverse_edge N lowpt1 lowpt2 ND' START) (incidence' (multigraph \<sigma>) v) \<sigma>) =
       root (fold (traverse_edge N lowpt1 lowpt2 ND' START) es ?\<sigma>')"
      by (simp add: Cons.hyps(2)[symmetric])
    also have "... = root ?\<sigma>'"
    proof -
      have "es = incidence' (multigraph ?\<sigma>') v"
        thm Cons.prems(1)
        thm Cons.hyps(2)
        sorry
      moreover have "path_search_invar' N lowpt1 lowpt2 ND' START v ?\<sigma>'"
        sorry
      ultimately show ?thesis
        using Cons.prems(1)
        by (auto simp add: Cons.hyps(2)[symmetric] intro: Cons.hyps(1))
    qed
    also have "... = root \<sigma>"
    proof (cases "tree_arc e \<sigma>")
      case True
      thm traverse_edge_def
      hence
        "root (traverse_edge N lowpt1 lowpt2 ND' START e \<sigma>) =
         root (path_search N lowpt1 lowpt2 ND' START (head e) (if START e then while_loop_1 \<sigma> else \<sigma>))"
        by (simp add: traverse_edge_def Let_def root_while_loop_3 root_while_loop_2 root_algorithm_6 root_algorithm_5)
      also have "... = root (if START e then while_loop_1 \<sigma> else \<sigma>)"
      proof -
        have "e \<in> set (incidence' (multigraph \<sigma>) v)"
          by (simp add: Cons.hyps(2)[symmetric])
        moreover have "path_search_invar' N lowpt1 lowpt2 ND' START v (if START e then while_loop_1 \<sigma> else \<sigma>)"
          sorry
        ultimately show ?thesis
          using True
          by (auto dest: Cons.prems(1))
      qed
      also have "... = root \<sigma>"
        by (simp add: root_while_loop_1)
      finally show ?thesis
        .
    next
      case False
      thus ?thesis
        using root_while_loop_4
        by (simp add: traverse_edge_def Let_def)
    qed
    finally show ?case
      .
  qed
  thus ?case
    using "1.prems"
    by (simp add: path_search_simps)
qed
*)

lemma (in algorithm_3_pre_valid_input) set_ESTACK_eq_A:
  shows "set (ESTACK \<sigma>') = P.A (multigraph \<sigma>')"
proof -
  have "set (ESTACK \<sigma>') = set (flatten (T_lookup (tree \<sigma>')) (incidence' (multigraph \<sigma>')) (root \<sigma>'))"
    unfolding path_search_invar_2 root_path_search
    by (simp add: init_def)
  also have "... = E (agublagu_2 (T_lookup (tree \<sigma>')) (incidence' (multigraph \<sigma>')) (root \<sigma>'))"
    by (simp add: a01)
  also have "... = E (incidence' (multigraph \<sigma>'))"
    using path_search_invar_\<sigma>'
    by
      (fastforce
        simp add: a02
        dest: path_search_invar.palm_tree palm_treeD(1))
  also have "... = P.A (multigraph \<sigma>')"
    by (simp add: E_incidence'_eq_A)
  finally show ?thesis
    .
qed

(* QUESTION: Define abbreviation for map set (map (map undirect))? *)
lemma (in algorithm_3_pre_valid_input) algorithm_3_correct:
  shows "are_split_components (undirect ` P.A P) (map set (map (map undirect) (algorithm_3 r T P N)))"
  unfolding algorithm_3_def Let_def
proof (intro are_split_componentsI_2, goal_cases)
  case 1
  have "Multigraph.finite_multigraph other (undirect ` set (ESTACK \<sigma>'))"
    using path_search_invar_\<sigma>'
    by
      (auto
        simp add: set_ESTACK_eq_A
        dest: path_search_invar.finite_multigraph_multigraph)
  moreover have "Ball (set (map set (map (map undirect) (Cs \<sigma>')))) (Multigraph.finite_multigraph other)"
    using path_search_invar_\<sigma>'
    by (auto simp add: dest: path_search_invar.finite_multigraph_Cs)
  ultimately show ?case
    by simp
next
  case 2
  show ?case
    using path_search_invar_mem_V set_ESTACK_eq_A
    by (simp add: init_def)
next
  case 3
  have "\<not> (\<exists>a b. is_separation_pair (undirect ` set (ESTACK \<sigma>')) a b)"
  proof
    assume "\<exists>a b. is_separation_pair (undirect ` set (ESTACK \<sigma>')) a b"
    then obtain a b where
      is_separation_pair: "is_separation_pair (undirect ` P.A (state.multigraph \<sigma>')) a b"
      by (auto simp add: set_ESTACK_eq_A)
    hence
      "a \<notin> Directed_Multigraph.V (E (incidence' (multigraph \<sigma>'))) \<or>
       b \<notin> Directed_Multigraph.V (E (incidence' (multigraph \<sigma>')))"
      using path_search_invar_\<sigma>' root_path_search
      by
        (fastforce
          simp add: init_def idk_20
          dest: path_search_invar_4 path_search_invar.palm_tree)
    thus False
      using is_separation_pair
      by (auto simp add: E_incidence'_eq_A V_image_undirect_eq dest: separation_pair_mem_V)
  qed
  moreover have "\<forall>G\<in>set (map set (map (map undirect) (Cs \<sigma>'))). \<not> (\<exists>a b. is_separation_pair G a b)"
    using path_search_invar_\<sigma>'
    by (auto simp add: dest: path_search_invar.no_separation_pair_Cs)
  ultimately show ?case
    by simp
qed

lemma (in algorithm_3_valid_input) algorithm_3'_correct:
  shows "are_split_components (P.E G) (map set (algorithm_3' G r))"
  unfolding image_undirect_A_eq_E[symmetric] algorithm_3'_def
  using algorithm_3_correct
  .

end