theory Connected_Component
  imports
    Path_Tbd
begin

section \<open>Connected components induced by a vertex\<close>

thm Berge.connected_component_def

subsection \<open>@{term component_edges}\<close>

subsubsection \<open>\<close>

lemma mem_component_edgesD:
  assumes "{u, v} \<in> component_edges G C"
  shows
    "{u, v} \<in> G"
    "u \<in> C"
    "v \<in> C"
  using assms
  by (auto simp add: component_edges_def insert_commute doubleton_eq_iff)

lemma mem_component_edgesI:
  assumes "{u, v} \<in> G"
  assumes "{u, v} \<subseteq> C"
  shows "{u, v} \<in> component_edges G C"
  using assms
  by (auto simp add: component_edges_def)

lemma mem_component_edgesI_2:
  assumes "{u, v} \<in> G"
  assumes "u \<in> C"
  assumes "v \<in> C"
  shows "{u, v} \<in> component_edges G C"
  using assms
  by (intro mem_component_edgesI) simp+

lemma component_edges_subsetI:
  assumes "\<And>x y. {x, y} \<in> component_edges G C \<Longrightarrow> {x, y} \<in> S"
  shows "component_edges G C \<subseteq> S"
  using assms
  by (auto simp add: component_edges_def)

subsubsection \<open>\<close>

lemma Vs_component_edges_subset:
  shows "Vs (component_edges G C) \<subseteq> C"
  by (auto simp add: Vs_def component_edges_def)

subsection \<open>@{term "component_edges G \<circ> Berge.connected_component G"}\<close>

subsubsection \<open>\<close>

lemma mem_component_edges_connected_componentI:
  assumes "{u, v} \<in> G"
  shows "{u, v} \<in> component_edges G (Berge.connected_component G u)"
  using assms
proof (rule mem_component_edgesI_2, goal_cases)
  case 1
  show ?case
    using in_own_connected_component
    .
next
  case 2
  show ?case
    using assms
    by (auto intro: edges_are_walks)
qed

subsubsection \<open>\<close>

lemma walk_betw_connected_componentD:
  assumes "walk_betw G u p v"
  shows
    "set p \<subseteq> Berge.connected_component G u"
    "set (edges_of_path p) \<subseteq> component_edges G (Berge.connected_component G u)"
proof -
  let ?C = "Berge.connected_component G u"
  show "set p \<subseteq> ?C"
    using assms
    unfolding walk_between_nonempty_path(3)[OF assms, symmetric]
    by (intro walk_between_nonempty_path(1) path_subset_conn_comp)
  thus "set (edges_of_path p) \<subseteq> component_edges G ?C"
    using assms
    by (intro walk_between_nonempty_path(1) edges_path_subset_edges)
qed

lemma mem_connected_componentE_2:
  assumes "{u, v} \<in> G"
  assumes "x \<in> Berge.connected_component G u"
  obtains p where
    "walk_betw (component_edges G (Berge.connected_component G u)) u p x"
proof (cases "u = x")
  case True
  have "u \<in> Vs (component_edges G (Berge.connected_component G u))"
    using assms(1)
    by (intro mem_component_edges_connected_componentI edges_are_Vs)
  thus ?thesis
    by (fastforce simp add: True intro: walk_reflexive that)
next
  case False
  let ?C = "Berge.connected_component G u"
  obtain p where
    walk_betw_p: "walk_betw G u p x"
    using assms
    by (elim in_connected_component_has_path) (intro edges_are_Vs)
  hence "set (edges_of_path p) \<subseteq> component_edges G ?C"
    by (intro walk_betw_connected_componentD(2))
  moreover have "walk_betw (set (edges_of_path p)) u p x"
    using walk_betw_p False
    by (intro length_ge_2I walk_betw_in_set_edges_of_path)
  ultimately show ?thesis
    by (intro that) (rule walk_subset)
qed

section \<open>Connected components induced by an edge\<close>

definition connected_component :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "connected_component G e \<equiv> {e'. \<exists>p. path G p \<and> e \<in> set (edges_of_path p) \<and> e' \<in> set (edges_of_path p)}"

subsubsection \<open>\<close>

lemma mem_connected_componentE':
  assumes "e' \<in> connected_component G e"
  obtains p where
    "path G p \<and> e \<in> set (edges_of_path p) \<and> e' \<in> set (edges_of_path p)"
  using assms
  by (auto simp add: connected_component_def)

subsubsection \<open>\<close>

lemma mem_connected_componentE_2':
  assumes "{x, y} \<in> connected_component G {u, v}"
  obtains p where
    "walk_betw (connected_component G {u, v}) u p x"
proof (cases "u = x")
  case True
  have "x \<in> Vs (connected_component G {u, v})"
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
    using assms
    by (auto elim: mem_connected_componentE')
  then obtain p' where
    walk_betw_p': "walk_betw G u p' x" and
    "set (edges_of_path p') \<subseteq> set (edges_of_path p)"
    by (metis tbdE set_edges_of_path_sublist_subset_2)
  hence "set (edges_of_path p') \<subseteq> connected_component G {u, v}"
    using p(1, 2)
    by (auto simp add: connected_component_def)
  moreover have "walk_betw (set (edges_of_path p')) u p' x"
    using walk_betw_p' False
    by (intro length_ge_2I walk_betw_in_set_edges_of_path)
  ultimately show ?thesis
    by (intro that) (rule walk_subset)
qed

lemma connected_component_subset_graph:
  shows "connected_component G e \<subseteq> G"
  by (auto simp add: connected_component_def intro: path_ball_edges)

lemma mem_connected_componentE_3':
  assumes "{x, y} \<in> connected_component G {u, v}"
  obtains p where
    "walk_betw G u p x"
  using assms connected_component_subset_graph
  by (fastforce elim: mem_connected_componentE_2' dest: walk_subset)

subsubsection \<open>\<close>

lemma connected_component_refl:
  assumes "{u, v} \<in> G"
  shows "{u, v} \<in> connected_component G {u, v}"
  using assms
  by (fastforce simp add: connected_component_def dest: edges_are_walks)

subsection \<open>Relation with @{term Berge.connected_component}}\<close>

lemma component_edges_connected_component_cong:
  assumes "{u, v} \<in> G"
  shows "component_edges G (Berge.connected_component G u) = connected_component G {u, v}"
proof (standard, goal_cases)
  case 1
  { fix x y
    assume assm: "{x, y} \<in> component_edges G (Berge.connected_component G u)"
    then obtain p where
      "walk_betw G u p x"
      using assms
      by
        (auto
         simp add: component_edges_def doubleton_eq_iff
         intro: edges_are_Vs in_connected_component_has_path)
    hence
      "walk_betw G v (v # p @ [y]) y \<and>
       {u, v} \<in> set (edges_of_path (v # p @ [y])) \<and>
       {x, y} \<in> set (edges_of_path (v # p @ [y]))"
      using assms assm
      by (auto simp add: insert_commute dest: mem_component_edgesD(1) walk_betw_Cons_snocI)
    hence "{x, y} \<in> connected_component G {u, v}"
      by (auto simp add: connected_component_def) }
  thus ?case
    by (auto simp add: component_edges_def)
next
  case 2
  { fix x y
    assume assm: "{x, y} \<in> connected_component G {u, v}"
    then obtain p where "walk_betw G u p x"
      by (elim mem_connected_componentE_3')
    moreover obtain p' where "walk_betw G u p' y"
      using assm
      by (auto simp add: insert_commute intro: mem_connected_componentE_3'[where ?x = y and ?y = x])
    ultimately have "{x, y} \<in> component_edges G (Berge.connected_component G u)"
      using connected_component_subset_graph assm
      by (force simp add: component_edges_def) }
  thus ?case
    by (force intro: mem_connected_componentE' v_in_edge_in_path_inj)
qed

lemma Vs_component_edges_connected_component_cong:
  assumes "{u, v} \<in> G"
  shows "Vs (component_edges G (Berge.connected_component G u)) = Berge.connected_component G u"
proof (standard, goal_cases)
  case 1
  thus ?case
    using Vs_component_edges_subset
    .
next
  case 2
  let ?C = "Berge.connected_component G u"
  { fix x
    assume assm: "x \<in> ?C"
    then obtain y where
      "{x, y} \<in> component_edges G ?C"
    proof (cases "x = u")
      case True
      thus ?thesis
        using assms
        by (auto intro: mem_component_edges_connected_componentI that)
    next
      case False
      obtain p where
        "walk_betw (component_edges G ?C) u p x"
        using assms assm
        by (elim mem_connected_componentE_2)
      thus ?thesis
        using False
        by (auto elim: walk_imp_edge_2 intro: length_ge_2I that)
    qed
    hence "x \<in> Vs (component_edges G ?C)"
      by (intro edges_are_Vs) }
  thus ?case
    by blast
qed

lemma (in graph) Vs_component_edges_connected_component_cong:
  assumes "u \<in> Vs G"
  shows "Vs (component_edges G (Berge.connected_component G u)) = Berge.connected_component G u"
  using assms
  by (auto elim: mem_VsE dest: Vs_component_edges_connected_component_cong)

end