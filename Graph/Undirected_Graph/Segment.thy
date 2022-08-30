(* TODO Rename. *)
theory Segment
  imports
    Walk
begin

definition tbd :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) edge \<Rightarrow> ('a, 'b) multigraph" where
  "tbd G X e \<equiv>
   {e'. \<exists>p u v. walk G p u v \<and>
                e \<in> set p \<and>
                e' \<in> set p \<and>
                set (tl (butlast (walk_vertices p u))) \<inter> X = {}}"

(**)

(* TODO Use \<forall>v\<in>V. v \<notin> set (tl (butlast p)) instead of intersection? Or an implication? *)
definition tbd :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a graph" where
  "tbd G X e \<equiv>
   {e'. \<exists>p. path G p \<and>
            e \<in> set (edges_of_path p) \<and>
            e' \<in> set (edges_of_path p) \<and>
            set (tl (butlast p)) \<inter> X = {}}"

subsubsection \<open>\<close>

lemma mem_tbdE:
  assumes "e' \<in> tbd G X e"
  obtains p where
    "path G p \<and> e \<in> set (edges_of_path p) \<and> e' \<in> set (edges_of_path p) \<and> set (tl (butlast p)) \<inter> X = {}"
  using assms
  by (auto simp add: tbd_def)

lemma mem_tbdI:
  assumes "path G p"
  assumes "e \<in> set (edges_of_path p)"
  assumes "e' \<in> set (edges_of_path p)"
  assumes "set (tl (butlast p)) \<inter> X = {}"
  shows "e' \<in> tbd G X e"
  using assms
  by (auto simp add: tbd_def)

lemma tbd_subset_graphI:
  assumes "\<And>x y. {x, y} \<in> tbd G X e \<Longrightarrow> {x, y} \<in> S"
  shows "tbd G X e \<subseteq> S"
  using assms
  by (force intro: mem_tbdE v_in_edge_in_path_inj)

subsubsection \<open>\<close>

lemma tbd_subset_connected_component:
  shows "tbd G X e \<subseteq> connected_component G e"
  by (auto simp add: tbd_def connected_component_def)

lemma tbd_subset_graph:
  shows "tbd G X e \<subseteq> G"
  using tbd_subset_connected_component connected_component_subset_graph
  by (rule subset_trans)

lemma mem_tbdE_2:
  assumes "{x, y} \<in> tbd G X {u, v}"
  obtains p where
    "walk_betw (tbd G X {u, v}) u p x"
proof (cases "u = x")
  case True
  have "x \<in> Vs (tbd G X {u, v})"
    using assms
    by (intro edges_are_Vs)
  thus ?thesis
    using True
    by (auto intro: walk_reflexive that)
next
  case False
  obtain p where p:
    "path G p"
    "{u, v} \<in> set (edges_of_path p)"
    "{x, y} \<in> set (edges_of_path p)"
    "set (tl (butlast p)) \<inter> X = {}"
    using assms
    by (auto elim: mem_tbdE)
  then obtain p' where
    walk_betw_p': "walk_betw G u p' x" and
    "set (edges_of_path p') \<subseteq> set (edges_of_path p)"
    by (metis tbdE set_edges_of_path_sublist_subset_2)
  hence "set (edges_of_path p') \<subseteq> tbd G X {u, v}"
    using p(1, 2, 4)
    by (auto simp add: tbd_def)
  moreover have "walk_betw (set (edges_of_path p')) u p' x"
    using walk_betw_p' False
    by (intro length_ge_2I walk_betw_in_set_edges_of_path)
  ultimately show ?thesis
    by (intro that) (rule walk_subset)
qed

lemma mem_tbdE_3:
  assumes "{x, y} \<in> tbd G X {u, v}"
  obtains p where
    "walk_betw G u p x"
  using assms tbd_subset_graph
  by (fastforce elim: mem_tbdE_2 dest: walk_subset)

lemma tbd_refl:
  assumes "{u, v} \<in> G"
  shows "{u, v} \<in> tbd G X {u, v}"
  using assms
  by (fastforce simp add: tbd_def dest: edges_are_walks)

lemma tbd_symmetric:
  assumes "e' \<in> tbd G X e"
  shows "e \<in> tbd G X e'"
  using assms
  by (auto elim: mem_tbdE intro: mem_tbdI)

subsection \<open>Relation with @{term Berge.connected_component} and @{term connected_component}\<close>

subsubsection \<open>\<close>

text \<open>A connected component is a special case of a tbd.\<close>

lemma connected_component_tbd_cong:
  shows "connected_component G = tbd G {}"
  by (auto simp add: connected_component_def tbd_def)

subsubsection \<open>\<close>

(* TODO Rename. *)
(* TODO Can we avoid considering all possibilities, that is, whether e comes before or after e', and
the directions of e and e'? *)
thm path_split_edge
lemma bar:
  assumes "{x, y} \<in> tbd G X {u, v}"
  assumes "x \<in> X"
  assumes "y \<in> X"
  shows "{x, y} = {u, v}"
  sorry

(* TODO Rename. *)
lemma 1:
  assumes "{u, v} \<in> G"
  assumes "u \<in> X"
  assumes "v \<in> X"
  shows "tbd G X {u, v} = {{u, v}}"
proof (standard, goal_cases)
  case 1
  show ?case
  proof (rule tbd_subset_graphI)
    fix x y
    assume "{x, y} \<in> tbd G X {u, v}"
    thus "{x, y} \<in> {{u, v}}"
      using assms(2, 3)
      by (auto dest: tbd_symmetric bar)
  qed
next
  case 2
  show ?case
    using assms(1)
    by (auto intro: tbd_refl)
qed

lemma mem_tbdE_4:
  assumes "{x, y} \<in> tbd G X {u, v}"
  assumes "u \<notin> X"
  assumes "x \<notin> X"
  assumes "u \<noteq> x"
  obtains p where
    "walk_betw (G - incidence G X) u p x"
proof -
  obtain p where p:
    "path G p"
    "{u, v} \<in> set (edges_of_path p)"
    "{x, y} \<in> set (edges_of_path p)"
    "set (tl (butlast p)) \<inter> X = {}"
    using assms(1)
    by (auto elim: mem_tbdE)
  then obtain p' where p':
    "walk_betw G u p' x"
    "sublist p' p \<or> sublist p' (rev p)"
    by (elim tbdE)
  have "set (edges_of_path p') \<subseteq> G - incidence G X"
  proof -
    { fix e
      assume "e \<in> set (edges_of_path p') \<and> e \<in> incidence G X"
      then obtain a where
        "a \<in> set p'" and
        a_mem_V: "a \<in> X"
        by (auto simp add: incidence_def intro: v_in_edge_in_path_gen)
      then consider
        (hd) "a = hd p'" |
        (tl_butlast) "a \<in> set (tl (butlast p'))" |
        (last) "a = last p'"
        by (auto dest: mem_setD)
      hence False
      proof (cases)
        case hd
        thus ?thesis
          using p'(1) assms(2) a_mem_V
          by (simp add: walk_between_nonempty_path(3))
      next
        case tl_butlast
        thus ?thesis
          using p'(2) set_tl_butlast_sublist_subset_2 p(4) a_mem_V
          by auto
      next
        case last
        thus ?thesis
          using p'(1) assms(3) a_mem_V
          by (simp add: walk_between_nonempty_path(4))
      qed }
    thus ?thesis
      using p'(1) tbd_subset_graph
      by (fastforce dest: set_edges_of_path_subset)
  qed
  moreover have "walk_betw (set (edges_of_path p')) u p' x"
    using p'(1) assms(4)
    by (intro length_ge_2I walk_betw_in_set_edges_of_path)
  ultimately show ?thesis
    by (intro that) (rule walk_subset)
qed

(* TODO Rename. *)
lemma two_aux:
  assumes "u \<notin> X"
  assumes "{x, y} \<in> tbd G X {u, v}"
  assumes "x \<notin> X"
  shows
    "{x, y} \<in>
     component_edges (G - incidence G X) (Berge.connected_component (G - incidence G X) u) \<union>
     idk G (Berge.connected_component (G - incidence G X) u) X"
proof -
  let ?G' = "G - incidence G X"
  let ?C = "Berge.connected_component ?G' u"
  have x_mem: "x \<in> ?C"
  proof (cases "u = x")
    case True
    thus ?thesis
      using in_own_connected_component
      by force
  next
    case False
    thus ?thesis
      using assms(1-3)
      by (auto intro: mem_tbdE_4)
  qed
  show ?thesis
  proof (cases "y \<in> X")
    case True
    thus ?thesis
      using tbd_subset_graph assms(2) x_mem
      by (fastforce intro: mem_idkI)
  next
    case False
    hence "{x, y} \<in> ?G'"
      using tbd_subset_graph assms(2, 3)
      by (auto simp add: incidence_def)
    moreover hence "y \<in> ?C"
      using x_mem
      by (fastforce dest: connected_components_member_eq[symmetric] intro: edges_are_walks)
    ultimately show ?thesis
      using x_mem
      by (auto intro: mem_component_edgesI_2)
  qed
qed

(* TODO Rename. *)
lemma two_aux_2:
  assumes "{u, v} \<in> G"
  assumes "u \<notin> X"
  assumes "{x, y} \<in> G"
  assumes "x \<in> Berge.connected_component (G - incidence G X) u"
  shows "{x, y} \<in> tbd G X {u, v}"
proof -
  let ?G' = "G - incidence G X"
  let ?C = "Berge.connected_component ?G' u"
  obtain p where
    "walk_betw G u p x \<and> set p \<inter> X = {}"
  proof (cases "u = x")
    case True
    thus ?thesis
      using assms(1, 2)
      by (fastforce intro: edges_are_Vs walk_reflexive that)
  next
    case False
    hence "u \<in> Vs ?G'"
      using assms(4)
      by (auto dest: connected_components_member_sym in_connected_component_in_edges)
    then obtain p where
      "walk_betw ?G' u p x"
      using assms(4)
      by (elim in_connected_component_has_path)
    hence "walk_betw G u p x \<and> set p \<subseteq> Vs ?G'"
      using Diff_subset[of G "incidence G X"]
      by (blast dest: walk_in_Vs intro: walk_subset)
    thus ?thesis
      using Vs_minus_incidence_subset
      by (fast intro: that)
  qed
  hence
    "walk_betw G v (v # p @ [y]) y \<and>
     {u, v} \<in> set (edges_of_path (v # p @ [y])) \<and>
     {x, y} \<in> set (edges_of_path (v # p @ [y])) \<and>
     set (tl (butlast (v # p @ [y]))) \<inter> X = {}"
    using assms(1, 3)
    by (auto simp add: insert_commute dest: walk_betw_Cons_snocI)
  thus ?thesis
    by (fastforce dest: walk_between_nonempty_path(1) intro: mem_tbdI)
qed

(* TODO Rename. *)
lemma 2:
  assumes "{u, v} \<in> G"
  assumes "u \<notin> X"
  shows
    "tbd G X {u, v} =
     component_edges (G - incidence G X) (Berge.connected_component (G - incidence G X) u) \<union>
     idk G (Berge.connected_component (G - incidence G X) u) X"
proof (standard, goal_cases)
  case 1
  let ?G' = "G - incidence G X"
  let ?C = "Berge.connected_component ?G' u"
  show ?case
  proof (rule tbd_subset_graphI)
    fix x y
    assume assm: "{x, y} \<in> tbd G X {u, v}"
    consider
      "x \<in> X \<and> y \<in> X" |
      "x \<notin> X" |
      "y \<notin> X"
      by fast
    thus "{x, y} \<in> component_edges ?G' ?C \<union> idk G ?C X"
    proof (cases)
      case 1
      thus ?thesis
        using assms(2) assm
        by (auto dest: bar)
    next
      case 2
      thus ?thesis
        using assms(2) assm
        by (intro two_aux)
    next
      case 3
      thus ?thesis
        using assms(2) assm
        by (auto simp add: insert_commute dest: two_aux[where ?x = y and ?y = x])
    qed
  qed
next
  case 2
  let ?G' = "G - incidence G X"
  let ?C = "Berge.connected_component ?G' u"
  have "component_edges ?G' ?C \<subseteq> tbd G X {u, v}"
  proof (rule component_edges_subsetI)
    fix x y
    assume "{x, y} \<in> component_edges ?G' ?C"
    thus "{x, y} \<in> tbd G X {u, v}"
      using assms
      by (auto dest: mem_component_edgesD(1, 2) intro: two_aux_2)
  qed
  moreover have "idk G ?C X \<subseteq> tbd G X {u, v}"
  proof (rule idk_subsetI)
    fix x y
    assume assm: "{x, y} \<in> idk G ?C X"
    then consider
      (x) "x \<in> ?C" |
      (y) "y \<in> ?C"
      by (auto dest: mem_idkD(2))
    thus "{x, y} \<in> tbd G X {u, v}"
    proof (cases)
      case x
      thus ?thesis
        using assms assm
        by (auto dest: mem_idkD(1) intro: two_aux_2)
    next
      case y
      hence "{y, x} \<in> tbd G X {u, v}"
        using assms assm
        by (fastforce simp add: insert_commute dest: mem_idkD(1) intro: two_aux_2)
      thus ?thesis
        by (simp add: insert_commute)
    qed    
  qed
  ultimately show ?case
    by blast
qed

(* TODO Rename. *)
lemma 3:
  assumes "{u, v} \<in> G"
  assumes "u \<notin> X"
  assumes "v \<notin> X"
  shows
    "tbd G X {u, v} =
     connected_component (G - incidence G X) {u, v} \<union>
     idk G (Vs (connected_component (G - incidence G X) {u, v})) X"
proof -
  let ?G' = "G - incidence G X"
  let ?C = "connected_component ?G' {u, v}"
  let ?C' = "Berge.connected_component ?G' u"
  have "tbd G X {u, v} = component_edges ?G' ?C' \<union> idk G ?C' X"
    using assms(1, 2)
    by (intro 2)
  also have "... = ?C \<union> idk G (Vs ?C) X"
  proof -
    have "{u, v} \<in> ?G'"
      using assms
      by (auto simp add: incidence_def idk_def)
    thus ?thesis
      by (simp add: component_edges_connected_component_cong[symmetric] Vs_component_edges_connected_component_cong)
  qed
  finally show ?thesis
    .
qed

subsection \<open>\<close>

definition tbds :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a graph set" where
  "tbds G X \<equiv> {S. \<exists>e. e \<in> G \<and> S = tbd G X e}"

lemma tbds_image_cong:
  shows "tbds G X = (tbd G X) ` G"
  by (auto simp add: tbds_def)

end