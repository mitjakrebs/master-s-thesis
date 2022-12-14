theory Graph
  imports
    "/Users/mitjakrebs/Documents/4_archives/2022_idp/thys/Graph/Undirected_Graph/Undirected_Graph"
begin

subsection \<open>\<close>

(* TODO Rename. *)
(* TODO Generalize to arbitrary edges? *)
definition idk :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a graph" where
  "idk G U V \<equiv> {{u, v} |u v. {u, v} \<in> G \<and> u \<in> U \<and> v \<in> V}"

subsubsection \<open>\<close>

lemma mem_idkD:
  assumes "{u, v} \<in> idk G U V"
  shows
    "{u, v} \<in> G"
    "u \<in> U \<or> v \<in> U"
    "u \<in> V \<or> v \<in> V"
  using assms
  by (auto simp add: idk_def insert_commute)

lemma mem_idkI:
  assumes "{u, v} \<in> G"
  assumes "u \<in> U"
  assumes "v \<in> V"
  shows "{u, v} \<in> idk G U V"
  using assms
  by (auto simp add: idk_def)

lemma idk_subsetI:
  assumes "\<And>x y. {x, y} \<in> idk G U V \<Longrightarrow> {x, y} \<in> S"
  shows "idk G U V \<subseteq> S"
  using assms
  by (auto simp add: idk_def)

subsubsection \<open>\<close>

lemma idk_subset:
  shows "idk G U V \<subseteq> G"
  by (auto simp add: idk_def)

subsection \<open>Incidence\<close>

definition incidence :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a graph" where
  "incidence G V \<equiv> {e. e \<in> G \<and> e \<inter> V \<noteq> {}}"

subsubsection \<open>\<close>

lemma Vs_minus_incidence_subset:
  shows "Vs (G - incidence G V) \<subseteq> Vs G - V"
proof
  fix v
  assume assm: "v \<in> Vs (G - incidence G V)"
  hence "v \<in> Vs G"
    by (auto intro: vs_transport)
  moreover have "v \<notin> V"
  proof
    obtain e where
      "e \<in> G - incidence G V"
      "v \<in> e"
      using assm
      by (elim vs_member_elim)
    moreover assume "v \<in> V"
    ultimately show False
      by (auto simp add: incidence_def)
  qed
  ultimately show "v \<in> Vs G - V"
    by blast
qed

(*
definition incidence :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a graph" where
  "incidence G V \<equiv> idk G V (Vs G)"

lemma mem_incidenceI:
  assumes "{u, v} \<in> G"
  assumes "u \<in> V"
  assumes "v \<in> Vs G"
  shows "{u, v} \<in> incidence G V"
  using assms
  by (auto simp add: incidence_def intro: mem_idkI)

lemma (in graph) Vs_minus_incidence_subset:
  shows "Vs (G - incidence G V) \<subseteq> Vs G - V"
proof
  fix v
  assume assm: "v \<in> Vs (G - incidence G V)"
  hence "v \<in> Vs G"
    by (auto intro: vs_transport)
  moreover have "v \<notin> V"
  proof
    obtain w where
      "{v, w} \<in> G - incidence G V"
      using Diff_subset assm
      by (metis graph_subset graph.mem_VsE)
    moreover assume "v \<in> V"
    ultimately show False
      by (fastforce simp add: insert_commute intro: edges_are_Vs[of w v] mem_incidenceI)
  qed
  ultimately show "v \<in> Vs G - V"
    by blast
qed
*)

end