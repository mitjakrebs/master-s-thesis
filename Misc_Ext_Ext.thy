theory Misc_Ext_Ext
  imports
    Main
begin

lemma tl_rev:
  "tl (rev p) = rev (butlast p)"
  by (induct p) auto

lemma tl_butlast_rev:
  shows "tl (butlast (rev l)) = rev (tl (butlast l))"
  unfolding butlast_rev tl_rev butlast_tl
  ..

lemma mem_setD:
  assumes "x \<in> set l"
  shows "x = hd l \<or> x \<in> set (tl (butlast l)) \<or> x = last l"
proof (cases "l = []")
  case True
  thus ?thesis
    using assms
    by fastforce
next
  case l_non_empty: False
  show ?thesis
  proof (cases "tl l = []")
    case True
    thus ?thesis
      using l_non_empty assms
      by (auto simp add: tl_Nil)
  next
    case False
    have "hd l # tl (butlast l) @ [last l] = l"
    proof -
      have "hd l # tl (butlast l) @ [last l] = hd l # tl (butlast l @ [last l])"
      proof -
        have "0 < length (tl l)"
          using False
          by blast
        hence "0 < length (butlast l)"
          by simp
        hence "butlast l \<noteq> []"
          by fast
        thus ?thesis
          by simp
      qed
      also have "... = hd l # tl l"
        using l_non_empty
        by auto
      also have "... = l"
        using l_non_empty
        by fastforce
      finally show ?thesis
        .
    qed
    thus ?thesis
      using assms
      by (metis set_ConsD set_rotate1 rotate1.simps(2))
  qed
qed

lemma split_list_2:
  assumes "x \<in> set l"
  assumes "y \<in> set l"
  assumes "x \<noteq> y"
  obtains l1 l2 l3 where
    "l1 @ x # l2 @ y # l3 = l \<or> l1 @ x # l2 @ y # l3 = rev l"
proof -
  obtain l1 l2 where
    l1_l2: "l1 @ x # l2 = l"
    using assms(1)
    by (blast dest: split_list)
  then consider
    (l1) "y \<in> set l1" |
    (l2) "y \<in> set l2"
    using assms(2, 3)
    by fastforce
  then obtain l3 l4 l5 where
    "l3 @ x # l4 @ y # l5 = l \<or> l3 @ x # l4 @ y # l5 = rev l"
  proof (cases)
    case l1
    then obtain l3 l4 where
      "l3 @ y # l4 @ x # l2 = l"
      using l1_l2
      by (auto dest: split_list)
    thus ?thesis
      by (auto intro: that)
  next
    case l2
    then obtain l3 l4 where
      "l1 @ x # l3 @ y # l4 = l"
      using l1_l2
      by (auto dest: split_list)
    thus ?thesis
      by (auto intro: that)
  qed
  thus ?thesis
    by (intro that)
qed

end