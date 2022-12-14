theory Triconnectivity
  imports
    Connectivity
    Idk
    "../../Partitions_Ext"
begin

subsection \<open>Separation classes\<close>

definition (in other) separation_class :: "('a, 'b) multigraph \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) edge \<Rightarrow> ('a, 'b) multigraph" where
  "separation_class G a b \<equiv> tbd G {a, b}"

lemma (in other) separation_class_subset:
  shows "separation_class G a b e \<subseteq> G"
  unfolding separation_class_def
  by (intro tbd_subset)

lemma (in other) V_separation_class_subset:
  shows "V (separation_class G a b e) \<subseteq> V G"
  unfolding V_def
  using separation_class_subset
  by fast

(* QUESTION: Should we allow the empty set? *)
definition (in other) separation_classes :: "('a, 'b) multigraph \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) multigraph set" where
  "separation_classes G a b \<equiv> {E. \<exists>e\<in>G. E = separation_class G a b e}"

lemma (in other) separation_classes_tbds_cong:
  shows "separation_classes G a b = tbds G {a, b}"
  unfolding separation_classes_def separation_class_def tbds_def
  ..

lemma (in other) separation_classes_image_cong:
  shows "separation_classes G a b = (separation_class G a b) ` G"
  by (auto simp add: separation_classes_def)

lemma (in other) separation_class_subset_2:
  assumes "E1 \<in> separation_classes G a b"
  shows "E1 \<subseteq> G"
  using assms separation_class_subset
  by (fastforce simp add: separation_classes_def)

lemma (in other) V_separation_class_subset_2:
  assumes "E1 \<in> separation_classes G a b"
  shows "V E1 \<subseteq> V G"
  using assms V_separation_class_subset
  by (fastforce simp add: separation_classes_def)

lemma (in finite_multigraph) finite_separation_classes:
  shows "finite (separation_classes G a b)"
  using finite_edges
  by (simp add: separation_classes_image_cong)

lemma (in other) separation_class_68:
  assumes "E1 \<in> separation_classes G a b"
  assumes "E2 \<in> separation_classes G a b"
  assumes "E1 \<noteq> E2"
  shows "E1 \<inter> E2 = {}"
  sorry

lemma (in other) separation_class_69:
  assumes "E1 \<in> separation_classes G a b"
  assumes "E2 \<in> separation_classes G a b"
  assumes "E1 \<noteq> E2"
  shows "V E1 \<inter> V E2 = {a, b}"
  sorry

lemma (in other) separation_class_20:
  assumes "E G X \<in> separation_classes G a b"
  shows "V (E G X) = X \<union> {a, b}"
  sorry

subsection \<open>Separation pairs\<close>

definition (in other) is_case_1 :: "('a, 'b) multigraph \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "is_case_1 G a b \<equiv>
   \<exists>E1 E2. separation_classes G a b = {E1, E2} \<and> E1 \<noteq> E2 \<and>
           (card E1 = 1 \<or> card E2 = 1)"

lemma (in other) is_case_1E:
  assumes "is_case_1 G a b"
  obtains E1 E2 where
    "separation_classes G a b = {E1, E2}"
    "E1 \<noteq> E2"
    "card E1 = 1 \<or> card E2 = 1"
  using assms
  by (auto simp add: is_case_1_def)

definition (in other) is_case_2 :: "('a, 'b) multigraph \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "is_case_2 G a b \<equiv>
   \<exists>E1 E2 E3.
      separation_classes G a b = {E1, E2, E3} \<and> E1 \<noteq> E2 \<and> E2 \<noteq> E3 \<and>
      card E1 = 1 \<and> card E2 = 1 \<and> card E3 = 1"

lemma (in other) is_case_2E:
  assumes "is_case_2 G a b"
  obtains E1 E2 E3 where
    "separation_classes G a b = {E1, E2, E3}"
    "E1 \<noteq> E2"
    "E2 \<noteq> E3"
    "card E1 = 1"
    "card E2 = 1"
    "card E3 = 1"
  using assms
  by (auto simp add: is_case_2_def)

definition (in other) is_separation_pair :: "('a, 'b) multigraph \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "is_separation_pair G a b \<equiv>
   2 \<le> card (separation_classes G a b) \<and>
   \<not> is_case_1 G a b \<and>
   \<not> is_case_2 G a b"

lemma (in other) is_separation_pairD:
  assumes "is_separation_pair G a b"
  shows
    "2 \<le> card (separation_classes G a b)"
    "\<not> is_case_1 G a b"
    "\<not> is_case_2 G a b"
  using assms
  by (simp_all add: is_separation_pair_def)

(* TODO: Rename. *)
lemma (in other) separation_pair_mem_V:
  assumes "is_separation_pair G a b"
  shows
    "a \<in> V G"
    "b \<in> V G"
  using assms
  sorry

lemma (in other) is_separation_pairI:
  assumes "2 \<le> card (separation_classes G a b)"
  assumes "\<not> is_case_1 G a b"
  assumes "\<not> is_case_2 G a b"
  shows "is_separation_pair G a b"
  using assms
  by (simp add: is_separation_pair_def)

(* TODO: Move. *)
lemma card_ge_2_iff:
  assumes "finite S"
  shows "2 \<le> card S = (\<exists>e1 e2. e1 \<in> S \<and> e2 \<in> S \<and> e1 \<noteq> e2)"
  using assms
  by (auto dest: card_le_Suc0_iff_eq)

lemma (in other) is_separation_pairI_2:
  assumes "finite (separation_classes G a b)"
  assumes "E1 \<in> separation_classes G a b"
  assumes "2 \<le> card E1"
  assumes "E2 \<in> separation_classes G a b"
  assumes "2 \<le> card E2"
  assumes "E1 \<noteq> E2"
  shows "is_separation_pair G a b"
proof (rule is_separation_pairI, goal_cases)
  case 1
  show ?case
    using assms(1, 2, 4, 6)
    by (auto simp add: card_ge_2_iff)
next
  case 2
  show ?case
    using assms(2-6)
    by (force simp add: is_case_1_def)
next
  case 3
  show ?case
    using assms(2, 3)
    by (fastforce simp add: is_case_2_def)
qed

lemma (in other) is_separation_pairI_10:
  assumes "C1 \<in> connected_components (idk_4 G {a, b})"
  assumes "C2 \<in> connected_components (idk_4 G {a, b})"
  assumes "C2 \<noteq> C1"
  shows "is_separation_pair G a b"
  sorry

(**)

lemma (in other) separation_class_2:
  assumes "e \<in> G"
  shows "e \<in> separation_class G a b e"
  sorry

lemma (in other) separation_class_non_empty:
  assumes "E1 \<in> separation_classes G a b"
  shows "E1 \<noteq> {}"
  using assms
  by (auto simp add: separation_classes_def intro: separation_class_2)

lemma (in other) separation_class_1:
  assumes "v \<in> V G"
  assumes "v \<noteq> a"
  assumes "v \<noteq> b"
  obtains E where
    "E \<in> separation_classes G a b"
    "v \<in> V E"
  sorry

lemma (in other) separation_class_3:
  assumes "E1 \<in> separation_classes G a b"
  assumes "u \<in> V E1"
  assumes "v \<in> V E1"
  obtains p where
    "walk E1 p u v"
    "set (tl (butlast (walk_vertices p u))) \<inter> {a, b} = {}"
  sorry

lemma (in other) separation_class_4:
  assumes "E1 \<in> separation_classes G a b"
  assumes "u \<noteq> a"
  assumes "u \<noteq> b"
  assumes "u \<in> V E1"
  assumes "v \<noteq> a"
  assumes "v \<noteq> b"
  assumes "v \<in> V E1"
  obtains p where
    "walk E1 p u v"
    "set (walk_vertices p u) \<inter> {a, b} = {}"
  sorry

lemma (in biconnected_multigraph) card_separation_class_geq_2I:
  assumes "E1 \<in> separation_classes G a b"
  assumes "v \<noteq> a"
  assumes "v \<noteq> b"
  assumes "v \<in> V E1"
  shows "2 \<le> card E1"
  sorry

lemma (in other) is_separation_pairI_3:
  assumes "is_multiple_edge G {a, b}"
  assumes "4 \<le> card G"
  shows "is_separation_pair G a b"
proof (rule is_separation_pairI, goal_cases)
  case 1
  then show ?case sorry
next
  case 2
  then show ?case sorry
next
  case 3
  then show ?case sorry
qed

lemma (in other) card_geq_4I:
  assumes "is_separation_pair G a b"
  assumes "is_multiple_edge G {a, b}"
  shows "4 \<le> card G"
  sorry

lemma (in other) separation_class_10:
  assumes "is_separation_pair G a b"
  assumes "\<not> is_multiple_edge G {a, b}"
  assumes "E1 \<in> separation_classes G a b"
  obtains E2 v where
    "E2 \<in> separation_classes G a b"
    "E2 \<noteq> E1"
    "v \<in> V E2"
    "v \<noteq> a"
    "v \<noteq> b"
  sorry

(* TODO: Consider removing this lemma. *)
lemma (in other) separation_class_99:
  assumes "is_separation_pair G a b"
  assumes "\<not> is_multiple_edge G {a, b}"
  assumes "C1 \<in> connected_components (idk_4 G {a, b})"
  obtains C2 where
    "C2 \<in> connected_components (idk_4 G {a, b})"
    "C2 \<noteq> C1"
  sorry

lemma (in other) separation_class_11:
  assumes "is_separation_pair G a b"
  assumes "\<not> is_multiple_edge G {a, b}"
  assumes "E1 \<in> separation_classes G a b"
  obtains v where
    "v \<in> V G"
    "v \<notin> V E1"
  sorry

lemma (in other) separation_class_13:
  assumes "is_separation_pair G a b"
  assumes "\<not> is_multiple_edge G {a, b}"
  obtains C1 C2 where
    "C1 \<in> connected_components (idk_4 G {a, b})"
    "C2 \<in> connected_components (idk_4 G {a, b})"
    "C2 \<noteq> C1"
  sorry

(* TODO: Consider removing this lemma. *)
lemma (in other) separation_class_12:
  assumes "is_separation_pair G a b"
  assumes "\<not> is_multiple_edge G {a, b}"
  assumes "C \<in> connected_components (idk_4 G {a, b})"
  obtains v where
    "v \<in> V G"
    "v \<noteq> a"
    "v \<noteq> b"
    "v \<notin> C"
  sorry

subsection \<open>Split components\<close>

definition (in other) are_split_graphs where
  "are_split_graphs G G' G'' \<equiv>
   \<exists>a b Es' Es'' e.
      Es' \<union> Es'' = separation_classes G a b \<and>
      Es' \<inter> Es'' = {} \<and>
      2 \<le> card (\<Union> Es') \<and>
      2 \<le> card (\<Union> Es'') \<and>
      G' = \<Union> Es' \<union> {e} \<and>
      G'' = \<Union> Es'' \<union> {e} \<and>
      endpoints e = {a, b} \<and>
      e \<notin> G"

lemma (in other) are_split_graphsE:
  assumes "are_split_graphs G G' G''"
  obtains a b Es' Es'' e where
    "Es' \<union> Es'' = separation_classes G a b"
    "Es' \<inter> Es'' = {}"
    "2 \<le> card (\<Union> Es')"
    "2 \<le> card (\<Union> Es'')"
    "G' = \<Union> Es' \<union> {e}"
    "G'' = \<Union> Es'' \<union> {e}"
    "endpoints e = {a, b}"
    "e \<notin> G"
  using assms
  by (auto simp add: are_split_graphs_def)

lemma (in finite_multigraph) split_graphs_imp_separation_pair:
  assumes "are_split_graphs G G' G''"
  obtains a b where
    "is_separation_pair G a b"
proof -
  obtain a b Es' Es'' where
    *: "Es' \<union> Es'' = separation_classes G a b"
    "Es' \<inter> Es'' = {}"
    "2 \<le> card (\<Union> Es')"
    "2 \<le> card (\<Union> Es'')"
    using assms
    by (elim are_split_graphsE)
  have "is_separation_pair G a b"
  proof (intro is_separation_pairI, goal_cases)
    case 1
    obtain E' E'' where
      "E' \<in> Es'"
      "E'' \<in> Es''"
      using *(3, 4)
      by fastforce
    moreover hence "E' \<noteq> E''"
      using *(2)
      by auto
    ultimately show ?case
      using *(1) finite_separation_classes
      by (fastforce simp add: card_ge_2_iff)
  next
    case 2
    { assume "is_case_1 G a b"
      then obtain E1 E2 where
        E1_E2: "separation_classes G a b = {E1, E2}"
        "E1 \<noteq> E2"
        "card E1 = 1 \<or> card E2 = 1"
        by (elim is_case_1E)
      hence "Es' = {E1} \<and> Es'' = {E2} \<or> Es' = {E2} \<and> Es'' = {E1}"
        (* TODO: Beautify. *)
        using *
        by (smt (verit, best) Int_Un_eq(1) Int_insert_left_if0 Int_insert_left_if1 Un_Int_eq(2) Un_Int_eq(3) Union_empty equals0D finite.emptyI card_ge_2_iff other_axioms sup_commute)
      hence False
        using *(3-4) E1_E2(3)
        by fastforce }
    thus ?case
      by fast
  next
    case 3
    { assume "is_case_2 G a b"
      then obtain E1 E2 E3 where
        "separation_classes G a b = {E1, E2, E3}"
        "E1 \<noteq> E2"
        "E2 \<noteq> E3"
        "card E1 = 1"
        "card E2 = 1"
        "card E3 = 1"
        by (elim is_case_2E)
      hence False
        (* TODO: Beautify. *)
        using *
        by (smt (verit, ccfv_threshold) Int_Un_eq(4) Int_insert_right_if0 Int_insert_right_if1 Suc_1 Sup_empty Un_Int_eq(2) Un_Int_eq(3) Un_Int_eq(4) cSup_singleton empty_iff finite.intros(1) insert_iff lessI linorder_not_less card_ge_2_iff other_axioms) }
    thus ?case
      by blast
  qed
  thus ?thesis
    by (intro that)
qed

lemma (in finite_multigraph) split_graphs_if_separation_pair:
  assumes "is_separation_pair G a b"
  obtains G' G'' where
    "are_split_graphs G G' G''"
  sorry

(* QUESTION: Rename? *)
inductive (in other) is_split_image :: "('a, 'b) multigraph list \<Rightarrow> ('a, 'b) multigraph list \<Rightarrow> bool" where
  is_split_image_Nil_Nil: "is_split_image [] []" |
  is_split_image_Cons_Cons:
  "\<lbrakk> \<not> (\<exists>G' G''. are_split_graphs G G' G''); is_split_image Gs Gs' \<rbrakk> \<Longrightarrow>
   is_split_image (G # Gs) (G # Gs')" |
  is_split_image_Cons_Cons_Cons:
  "\<lbrakk> are_split_graphs G G' G''; is_split_image Gs Gs' \<rbrakk> \<Longrightarrow> is_split_image (G # Gs) (G' # G'' # Gs')"

declare (in other) is_split_image_Nil_Nil [simp]
inductive_simps (in other) is_split_image_Cons_Cons_iff [simp]: "is_split_image (G # Gs) (G' # Gs')"
inductive_simps (in other) is_split_image_Cons_Cons_Cons_iff [simp]: "is_split_image (G # Gs) (G' # G'' # Gs')"

lemma (in other) is_split_image_Cons_Cons_iff_2:
  shows
    "is_split_image (G # Gs) (G # Gs') \<longleftrightarrow>
     \<not> (\<exists>G' G''. are_split_graphs G G' G'') \<and> is_split_image Gs Gs'"
  by (auto simp add: are_split_graphs_def)

lemma (in finite_multigraph) is_split_image_Cons_Cons_iff_2:
  shows
    "is_split_image (G # Gs) (G # Gs') \<longleftrightarrow>
     \<not> (\<exists>a b. is_separation_pair G a b) \<and> is_split_image Gs Gs'"
  unfolding is_split_image_Cons_Cons_iff_2
  by (auto elim: split_graphs_imp_separation_pair split_graphs_if_separation_pair)

(* QUESTION: Rename? *)
lemma (in other) is_split_image_fixpoint_iff:
  shows "is_split_image Gs Gs \<longleftrightarrow> (\<forall>G\<in>set Gs. \<not> (\<exists>G' G''. are_split_graphs G G' G''))"
proof (induct Gs)
  case Nil
  show ?case
    by simp
next
  case (Cons G Gs)
  thus ?case
    unfolding is_split_image_Cons_Cons_iff_2
    by simp
qed

(* QUESTION: Rename? *)
lemma (in other) is_split_image_fixpoint_iff_2:
  assumes "Ball (set Gs) (finite_multigraph other)"
  shows "is_split_image Gs Gs \<longleftrightarrow> (\<forall>G\<in>set Gs. \<not> (\<exists>a b. is_separation_pair G a b))"
  using assms
  by
    (fastforce
      simp add: is_split_image_fixpoint_iff
      elim: finite_multigraph.split_graphs_imp_separation_pair finite_multigraph.split_graphs_if_separation_pair)

lemma (in other) length_split_image_geq:
  assumes "is_split_image Gs Gs'"
  shows "length Gs \<le> length Gs'"
  using assms
  by (induct rule: is_split_image.induct) simp+

(* QUESTION: Rename? *)
lemma (in other) is_split_image_fixpointI:
  assumes "is_split_image Gs Gs'"
  assumes "length Gs = length Gs'"
  shows "Gs = Gs'"
  using assms
  by (induct rule: is_split_image.induct) (auto dest: length_split_image_geq)

(* TODO: Rename. *)
definition (in other) is_split_tbd :: "('a, 'b) multigraph list \<Rightarrow> ('a, 'b) multigraph list \<Rightarrow> bool" where
  "is_split_tbd Gs Gs' \<equiv> (Gs, Gs') \<in> {(Gs, Gs'). is_split_image Gs Gs'}\<^sup>+"

(* TODO: Rename. *)
lemma (in other) length_split_tbd_geq:
  assumes "is_split_tbd Gs Gs'"
  shows "length Gs \<le> length Gs'"
  using assms
  unfolding is_split_tbd_def
  by (induct rule: trancl.induct) (auto dest: length_split_image_geq)

(* TODO: Rename. *)
lemma (in other) is_split_tbd_fixpointD:
  assumes "is_split_tbd Gs Gs"
  shows "\<forall>G\<in>set Gs. \<not> (\<exists>G' G''. are_split_graphs G G' G'')"
  using assms
  unfolding is_split_tbd_def
proof (cases rule: trancl.cases)
  case r_into_trancl
  thus ?thesis
    by (simp add: is_split_image_fixpoint_iff)
next
  case (trancl_into_trancl Gs')
  hence "length Gs' = length Gs"
    by (fastforce simp add: is_split_tbd_def[symmetric] dest: length_split_image_geq length_split_tbd_geq)
  hence "Gs' = Gs"
    using trancl_into_trancl(2)
    by (auto dest: is_split_image_fixpointI)
  thus ?thesis
    using trancl_into_trancl(2)
    by (simp add: is_split_image_fixpoint_iff)
qed

(* TODO: Rename. *)
lemma (in other) is_split_tbd_fixpointD_2:
  assumes "Ball (set Gs) (finite_multigraph other)"
  assumes "is_split_tbd Gs Gs"
  shows "\<forall>G\<in>set Gs. \<not> (\<exists>a b. is_separation_pair G a b)"
  using assms
  by (fastforce dest: is_split_tbd_fixpointD elim: finite_multigraph.split_graphs_if_separation_pair)

(* TODO: Rename. *)
lemma (in other) is_split_tbd_fixpoint_iff:
  shows "is_split_tbd Gs Gs \<longleftrightarrow> (\<forall>G\<in>set Gs. \<not> (\<exists>G' G''. are_split_graphs G G' G''))"
proof (standard, goal_cases)
  case 1
  thus ?case
    by (intro is_split_tbd_fixpointD)
next
  case 2
  thus ?case
    by (auto simp add: is_split_tbd_def is_split_image_fixpoint_iff)
qed

(* TODO: Rename. *)
lemma (in other) is_split_tbd_fixpoint_iff_2:
  assumes "Ball (set Gs) (finite_multigraph other)"
  shows "is_split_tbd Gs Gs \<longleftrightarrow> (\<forall>G\<in>set Gs. \<not> (\<exists>a b. is_separation_pair G a b))"
  using assms
  by
    (fastforce
      simp add: is_split_tbd_fixpoint_iff
      elim: finite_multigraph.split_graphs_imp_separation_pair finite_multigraph.split_graphs_if_separation_pair)

definition (in other) are_split_components :: "('a, 'b) multigraph \<Rightarrow> ('a, 'b) multigraph list \<Rightarrow> bool" where
  "are_split_components G Gs \<equiv> is_split_tbd [G] Gs \<and> is_split_tbd Gs Gs"

lemma (in other) are_split_componentsI:
  assumes "is_split_tbd [G] Gs"
  assumes "is_split_tbd Gs Gs"
  shows "are_split_components G Gs"
  using assms
  by (simp add: are_split_components_def)

lemma (in other) are_split_componentsI_2:
  assumes "Ball (set Gs) (finite_multigraph other)"
  assumes "is_split_tbd [G] Gs"
  assumes "\<forall>G\<in>set Gs. \<not> (\<exists>a b. is_separation_pair G a b)"
  shows "are_split_components G Gs"
  using assms
  by (auto simp add: is_split_tbd_fixpoint_iff_2 intro: are_split_componentsI)

definition merge :: "('a, 'b) multigraph \<Rightarrow> ('a, 'b) multigraph \<Rightarrow> ('a, 'b) edge \<Rightarrow> ('a, 'b) multigraph" where
  "merge G1 G2 e \<equiv> G1 \<union> G2 - {e}"

subsection \<open>Triconnected components\<close>

end