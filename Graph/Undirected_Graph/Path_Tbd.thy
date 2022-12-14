theory Path_Tbd
  imports
    Graph
    "../../Misc_Ext_Ext"
begin

lemma path_split_edge:
  assumes "{u, v} \<in> set (edges_of_path p)"
  obtains p1 p2 where
    "p1 @ u # v # p2 = p \<or> p1 @ u # v # p2 = rev p"
proof -
  obtain i where i:
    "i < length (edges_of_path p)"
    "edges_of_path p ! i = {u, v}"
    using assms
    by (auto simp add: in_set_conv_nth)
  hence Suc_i: "Suc i < length p"
    by (simp add: edges_of_path_length)
  hence "{u, v} = {p ! i, p ! Suc i}"
    unfolding i(2)[symmetric]
    by (intro edges_of_path_index)
  hence "take i p @ u # v # drop (Suc (Suc i)) p = p \<or> take i p @ v # u # drop (Suc (Suc i)) p = p"
    using i(1) Suc_i
    by (auto simp add: Cons_nth_drop_Suc doubleton_eq_iff)
  moreover have
    "rev (take i p @ v # u # drop (Suc (Suc i)) p) =
     take (length p - Suc (Suc i)) (rev p) @ u # v # drop (length p - i) (rev p)"
    by (auto simp add: rev_drop rev_take)
  ultimately have
    "take i p @ u # v # drop (Suc (Suc i)) p = p \<or>
     take (length p - Suc (Suc i)) (rev p) @ u # v # drop (length p - i) (rev p) = rev p"
    by presburger
  thus ?thesis
    by (auto intro: that)
qed

definition sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "sublist l' l \<equiv> \<exists>l1 l2. l1 @ l' @ l2 = l"

lemma sublistE:
  assumes "sublist l' l"
  obtains l1 l2 where
    "l1 @ l' @ l2 = l"
  using assms
  by (auto simp add: sublist_def)

lemma sublistI:
  assumes "l1 @ l' @ l2 = l"
  shows "sublist l' l"
  using assms
  by (auto simp add: sublist_def)

lemma sublist_singletonI:
  assumes "x \<in> set l"
  shows "sublist [x] l"
  using assms
  by (fastforce simp add: sublist_def dest: split_list)

lemma
  assumes "sublist l' l"
  shows "length l' \<le> length l"
  using assms
  by (auto simp add: sublist_def)

lemma set_sublist_subset:
  assumes "sublist l' l"
  shows "set l' \<subseteq> set l"
  using assms
  by (auto simp add: sublist_def)

lemma set_tl_butlast_sublist_subset:
  assumes "sublist l' l"
  shows "set (tl (butlast l')) \<subseteq> set (tl (butlast l))"
proof
  fix x
  assume "x \<in> set (tl (butlast l'))"
  then obtain i' where
    "i' < length (tl (butlast l'))"
    "tl (butlast l') ! i' = x"
    by (auto simp add: in_set_conv_nth)
  hence Suc_i':
    "Suc i' < length l' - 1"
    "l' ! Suc i' = x"
    by (simp_all add: nth_tl nth_butlast)
  obtain l1 l2 where
    l: "l1 @ l' @ l2 = l"
    using assms
    by (auto simp add: sublist_def)
  let ?i = "length l1 + Suc i'"
  have
    "?i < length l - 1"
    "l ! ?i = x"
    using Suc_i'
    by (auto simp add: l[symmetric] nth_append)
  hence
    "?i - 1 < length (tl (butlast l))"
    "tl (butlast l) ! (?i - 1) = x"
    by (simp_all add: nth_tl nth_butlast)
  thus "x \<in> set (tl (butlast l))"
    by (auto simp add: in_set_conv_nth)
qed

lemma set_edges_of_path_sublist_subset:
  assumes "sublist p' p"
  shows "set (edges_of_path p') \<subseteq> set (edges_of_path p)"
  using assms edges_of_path_append_subset set_edges_of_path_subset_append
  by (fastforce simp add: sublist_def)

lemma set_sublist_subset_2:
  assumes "sublist p' p \<or> sublist p' (rev p)"
  shows "set p' \<subseteq> set p"
  using assms
  by (fastforce dest: set_sublist_subset)

lemma set_edges_of_path_sublist_subset_2:
  assumes "sublist p' p \<or> sublist p' (rev p)"
  shows "set (edges_of_path p') \<subseteq> set (edges_of_path p)"
  using assms
  by (fastforce simp add: edges_of_path_rev[symmetric] dest: set_edges_of_path_sublist_subset)

lemma set_tl_butlast_sublist_subset_2:
  assumes "sublist p' p \<or> sublist p' (rev p)"
  shows "set (tl (butlast p')) \<subseteq> set (tl (butlast p))"
proof -
  consider
    (p) "sublist p' p" |
    (rev_p) "sublist p' (rev p)"
    using assms
    by blast
  thus ?thesis
  proof (cases)
    case p
    thus ?thesis
      by (intro set_tl_butlast_sublist_subset)
  next
    case rev_p
    hence "set (tl (butlast p')) \<subseteq> set (tl (butlast (rev p)))"
      by (intro set_tl_butlast_sublist_subset)
    thus ?thesis
      unfolding tl_butlast_rev set_rev
      .
  qed
qed

(* TODO Rename. *)
lemma tbdE:
  assumes "path G p"
  assumes "{u, v} \<in> set (edges_of_path p)"
  assumes "{x, y} \<in> set (edges_of_path p)"
  obtains p' where
    "walk_betw G u p' x"
    "sublist p' p \<or> sublist p' (rev p)"
proof (cases "u = x")
  case True
  hence "u \<in> Vs G"
    using assms(1, 2)
    by (auto intro: path_ball_edges edges_are_Vs)
  hence "walk_betw G u [u] x"
    by (auto simp add: True intro: walk_reflexive)
  moreover have "sublist [u] p"
    using assms(2)
    by (intro sublist_singletonI) (rule v_in_edge_in_path)
  ultimately show ?thesis
    by (intro that) simp+
next
  case False
  have
    "u \<in> set p"
    "x \<in> set p"
    using assms(2, 3)
    by (auto intro: v_in_edge_in_path)
  then obtain p1 p2 p3 where
    "p1 @ u # p2 @ x # p3 = p \<or> p1 @ u # p2 @ x # p3 = rev p"
    using False
    by (auto intro: split_list_2)
  then consider
    (p) "p1 @ u # p2 @ x # p3 = p" |
    (rev_p) "p1 @ u # p2 @ x # p3 = rev p"
    by fastforce
  thus ?thesis
  proof (cases)
    case p
    hence "walk_betw G u (u # p2 @ [x]) x"
      using assms(1)
      by (force intro: path_suff path_pref nonempty_path_walk_between)
    moreover have "sublist (u # p2 @ [x]) p"
      using p
      by (intro sublistI) simp
    ultimately show ?thesis
      by (intro that) simp+
  next
    case rev_p
    have "walk_betw G u (u # p2 @ [x]) x"
    proof -
      have "path G (rev p)"
        using assms(1)
        by (intro rev_path_is_path)
      thus ?thesis
        by (force simp add: rev_p[symmetric] intro: path_suff path_pref nonempty_path_walk_between)
    qed
    moreover have "sublist (u # p2 @ [x]) (rev p)"
      using rev_p
      by (intro sublistI) simp
    ultimately show ?thesis
      by (intro that) simp+
  qed
qed

end