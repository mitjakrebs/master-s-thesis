theory Hopcroft_Tarjan_Mutual_Recursion
  imports
    Hopcroft_Tarjan
begin

type_synonym ('a, 'b) component = "('a, 'b) Directed_Multigraph.edge list"

record ('b, 't, 'g, 'a) state =
  root :: 'b
  tree :: 't
  multigraph :: 'g
  ESTACK :: "('a, 'b) Directed_Multigraph.edge list"
  Cs :: "('a, 'b) component list"

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
  where insert = insert
  for other :: "('a::linorder, 'b::linorder) Multigraph.edge \<Rightarrow> 'b \<Rightarrow> 'b"
    and T_empty
    and T_update :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and T_delete
    and T_lookup
    and T_invar
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g" +
  fixes algorithm_5 :: "('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) Directed_Multigraph.edge \<Rightarrow> ('b, 't, 'g, 'a) state \<Rightarrow> ('b, 't, 'g, 'a) state"
  fixes algorithm_6 :: "('b \<Rightarrow> nat) \<Rightarrow> ('a, 'b) Directed_Multigraph.edge \<Rightarrow> ('b, 't, 'g, 'a) state \<Rightarrow> ('b, 't, 'g, 'a) state"
  assumes root_algorithm_5: "root (algorithm_5 N e \<sigma>) = root \<sigma>"
  assumes root_algorithm_6: "root (algorithm_6 N e \<sigma>) = root \<sigma>"
begin

definition tree_arc_2 where
  "tree_arc_2 e \<sigma> \<equiv> tree.tree_arc (T_lookup (tree \<sigma>)) e"

definition incidence_2 where
  "incidence_2 G \<equiv> Directed_Multigraph.incidence (\<lambda>v. incidence v G)"

function (domintros)
  path_search
  and fold' where
  "path_search N e \<sigma> =
   (if tree_arc_2 e \<sigma>
    then let \<sigma>1 = fold' N (incidence_2 (multigraph \<sigma>) (head e)) \<sigma>;
             \<sigma>2 = \<sigma>1\<lparr>ESTACK := e # ESTACK \<sigma>1\<rparr>;
             \<sigma>3 = algorithm_5 N e \<sigma>2;
             \<sigma>4 = algorithm_6 N e \<sigma>3
         in \<sigma>4
    else \<sigma>\<lparr>ESTACK := e # ESTACK \<sigma>\<rparr>)" |
  fold'_Nil: "fold' N [] \<sigma> = \<sigma>" |
  fold'_Cons: "fold' N (e # es) \<sigma> = fold' N es (path_search N e \<sigma>)"
  by pat_completeness simp+
thm path_search_fold'.pinduct

end

locale algorithm_3_pre = path_search
  where T_update = T_update
    and insert = insert
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
begin

definition init where
  "init r T P \<equiv>
   \<lparr>root = r,
    tree = T,
    multigraph = P,
    ESTACK = [],
    Cs = []\<rparr>"

definition algorithm_3 where
  "algorithm_3 r T P N \<equiv>
   let \<sigma> = path_search N (hd (Directed_Multigraph.incidence (\<lambda>v. incidence v P) r)) (init r T P)
   in ESTACK \<sigma> # Cs \<sigma>"

end

locale algorithm_3 = algorithm_3_pre
  where T_update = T_update
    and insert = insert
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g" +
  fixes T :: "'g \<Rightarrow> 'b \<Rightarrow> 't"
  fixes N :: "'g \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> nat"
  fixes I :: "'g \<Rightarrow> 'b \<Rightarrow> 'g"
  assumes steps_1_2_3_high_3:
    "\<lbrakk> biconnected_multigraph other (P.E G); r \<in> Multigraph.V (P.E G) \<rbrakk> \<Longrightarrow>
     steps_1_2_3_high_3 other r (\<lambda>v. incidence v (I G r)) (N G r) (P.E G) (T_lookup (T G r))"
begin

definition algorithm_3' :: "'g \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Multigraph.edge list list" where
  "algorithm_3' G r \<equiv> map (map undirect) (algorithm_3 r (T G r) (I G r) (N G r))"

end

subsection \<open>Verification of the correctness of the algorithm\<close>

subsubsection \<open>Assumptions on the input\<close>

locale path_search_valid_input = path_search
  where T_update = T_update
    and insert = insert
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g" +
  fixes N :: "'b \<Rightarrow> nat"
  fixes e :: "('a, 'b) Directed_Multigraph.edge"
  assumes "0 \<le> N (tail e)"
begin
end

locale algorithm_3_pre_valid_input = algorithm_3_pre
  where T_update = T_update
    and insert = insert
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g" +
  fixes r :: 'b
  fixes T :: 't
  fixes P :: 'g
  fixes N :: "'b \<Rightarrow> nat"
  assumes steps_1_2_3_high_2: "steps_1_2_3_high_2 r (\<lambda>v. incidence v P) (T_lookup T) N"
begin
sublocale path_search_valid_input
  where N = N
    and e = "hd (Directed_Multigraph.incidence (\<lambda>v. incidence v P) r)"
  sorry
end

abbreviation (in algorithm_3_pre) algorithm_3_pre_valid_input' where
  "algorithm_3_pre_valid_input' \<equiv>
   algorithm_3_pre_valid_input
    empty delete incidence invar
    other
    T_empty T_delete T_lookup T_invar
    algorithm_5
    algorithm_6
    T_update
    insert"

locale algorithm_3_valid_input = algorithm_3
  where T_update = T_update
    and insert = insert
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g" +
  fixes G :: 'g
  fixes r :: 'b
  assumes biconnected_multigraph: "biconnected_multigraph other (P.E G)"
  assumes r_mem_V: "r \<in> Multigraph.V (P.E G)"
begin
sublocale algorithm_3_pre_valid_input
  where T = "T G r"
    and P = "I G r"
    and N = "N G r"
  sorry
end

abbreviation (in algorithm_3) algorithm_3_valid_input' where
  "algorithm_3_valid_input' \<equiv>
   algorithm_3_valid_input
    empty delete incidence invar
    other
    T_empty T_delete T_lookup T_invar
    algorithm_5
    algorithm_6
    T
    N
    I
    T_update
    insert"

subsubsection \<open>Loop invariants\<close>

locale path_search_invar = path_search_valid_input
  where T_update = T_update
    and insert = insert
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g" +
  fixes \<sigma> :: "('b, 't, 'g, 'a) state"
    (* QUESTION: Use P.E instead? *)
  assumes finite_multigraph: "finite (undirect ` P.A (multigraph \<sigma>))"
  assumes simple_multigraph: "simple (undirect ` P.A (multigraph \<sigma>))"
  assumes finite_Cs: "Ball (set (map set (map (map undirect) (Cs \<sigma>)))) finite"
  assumes no_separation_pair_Cs: "\<forall>G\<in>set (map set (map (map undirect) (Cs \<sigma>))). \<not> (\<exists>a b. is_separation_pair G a b)"
    (* TODO: Order. *)
  assumes palm_tree_2: "palm_tree_2 (root \<sigma>) (T_lookup (tree \<sigma>)) (\<lambda>v. incidence v (multigraph \<sigma>))"
begin
end

abbreviation (in path_search) path_search_invar' where
  "path_search_invar' N e \<equiv>
   path_search_invar
    empty delete incidence invar
    other
    T_empty T_delete T_lookup T_invar
    algorithm_5
    algorithm_6
    N
    e
    T_update
    insert"

abbreviation (in path_search_valid_input) path_search_invar'' where
  "path_search_invar'' \<equiv> path_search_invar' N e"

lemma (in algorithm_3_pre_valid_input) path_search_invar_init:
  shows "path_search_invar' N (hd (Directed_Multigraph.incidence (\<lambda>v. incidence v P) r)) (init r T P)"
  sorry

subsubsection \<open>Termination\<close>

fun (in path_search) idk ::
  "('b \<Rightarrow> nat) \<times> ('a, 'b) Directed_Multigraph.edge \<times> ('b, 't, 'g, 'a) state +
   ('b \<Rightarrow> nat) \<times> ('a, 'b) Directed_Multigraph.edge list \<times> ('b, 't, 'g, 'a) state \<Rightarrow>
   nat" where
  "idk (Inl (_, _, \<sigma>)) = card (P.A (multigraph \<sigma>)) - length (ESTACK \<sigma>)" |
  "idk (Inr (_, es, _)) = length es"

function zig :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
and zag :: "'a graph \<Rightarrow> 'a graph \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  proper_zig: "zig G M v \<pi> \<sigma> = v # (
                    if \<exists>u. {u,v} \<in> M 
                    then zag G M (THE u. {u,v} \<in> M) \<pi> \<sigma>
                    else [])" if "matching M"
| no_matching_zig: "zig  M v  _ = [v]" if "\<not>matching M"

| proper_zag: "zag G M u \<pi> \<sigma> =  u # (if \<exists>v. {u,v} \<in> M
                      then 
                      (let v = THE v. {u,v} \<in> M in (
                        if \<exists>v'. shifts_to G M u v v' \<pi> \<sigma>
                        then zig G M (THE v'. shifts_to G M u v v' \<pi> \<sigma>) \<pi> \<sigma>
                        else [])
                      )
                      else []
                    )" if "matching M"
| no_matching_zag: "zag  M v  _ = [v]" if "\<not>matching M"
  by auto (metis prod_cases5 sumE)

definition zig_zag_relation where
  "zig_zag_relation \<equiv>
    {(Inr (G, M, u, \<pi>, \<sigma>), Inl (G, M, v, \<pi>, \<sigma>)) | (G :: 'a graph) M u v \<pi> \<sigma>. matching M \<and> {u,v} \<in> M \<and> ((\<exists>v'. shifts_to G M u v v' \<pi> \<sigma>) \<longrightarrow> index \<sigma> v < index \<sigma> (THE v'. shifts_to G M u v v' \<pi> \<sigma>))} \<union>
    {(Inl (G, M, v', \<pi>, \<sigma>), Inr (G, M, u, \<pi>, \<sigma>)) | (G :: 'a graph) M u v' \<pi> \<sigma>. matching M \<and> (\<exists>v. {u,v} \<in> M \<and> shifts_to G M u (THE v. {u,v} \<in> M) v' \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> M) < index \<sigma> v'}"

lemma (in path_search)
  shows
    "path_search_fold'_dom (Inl (N, e, \<sigma>))"
    "path_search_fold'_dom (Inr (N, incidence_2 (multigraph \<sigma>) (head e), \<sigma>))"
  
proof (induct "card (P.A (multigraph \<sigma>)) - length (ESTACK \<sigma>)" arbitrary: \<sigma> rule: less_induct)
  case less
  show "path_search_fold'_dom (Inl (N, e, \<sigma>))"
  proof (cases "tree_arc_2 e \<sigma>")
    case True
    show ?thesis
      sorry
  next
    case False
    thus ?thesis      
      by (fast intro: path_search_fold'.domintros(1))
  qed
  show "path_search_fold'_dom (Inr (N, incidence_2 (multigraph \<sigma>) (head e), \<sigma>))"
  proof (cases "incidence_2 (multigraph \<sigma>) (head e)")
    case Nil
    thus ?thesis
      by (auto intro: path_search_fold'.domintros(2))
  next
    case (Cons e es)
    then show ?thesis
      sorry
  qed
qed

lemma (in path_search_valid_input) path_search_fold'_dom_Inl:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_fold'_dom (Inl (N, e, \<sigma>))"
  sorry

lemma (in path_search_valid_input) path_search_fold'_dom_Inr:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_fold'_dom (Inr (N, incidence_2 (multigraph \<sigma>) (head e), \<sigma>))"
  sorry

lemma (in path_search_invar) path_search_fold'_dom_Inl:
  shows "path_search_fold'_dom (Inl (N, e, \<sigma>))"
  sorry

lemma (in path_search_invar) path_search_fold'_dom_Inr:
  shows "path_search_fold'_dom (Inr (N, incidence_2 (multigraph \<sigma>) (head e), \<sigma>))"
  sorry

lemma (in path_search) path_search_fold'_induct_1:
  assumes "path_search_invar' N e \<sigma>"
  assumes
    "\<And>N e \<sigma>.
        path_search_fold'_dom (Inl (N, e, \<sigma>)) \<Longrightarrow> (tree_arc_2 e \<sigma> \<Longrightarrow> Q N (incidence_2 (multigraph \<sigma>) (head e)) \<sigma>) \<Longrightarrow> P N e \<sigma>"
  assumes "\<And>N \<sigma>. Q N [] \<sigma>"
  assumes
    "\<And>N e es \<sigma>.
        path_search_fold'_dom (Inr (N, e # es, \<sigma>)) \<Longrightarrow> P N e \<sigma> \<Longrightarrow> Q N es (path_search N e \<sigma>) \<Longrightarrow> Q N (e # es) \<sigma>"
  shows
    "P N e \<sigma>"
  thm path_search_fold'.pinduct
proof (rule path_search_fold'.pinduct(1)[where ?Q = Q], goal_cases)
  case 1
  show ?case
    using assms(1)
    by (intro path_search_invar.path_search_fold'_dom_Inl)
next
  case (2 N e \<sigma>)
  thus ?case
    by (intro assms(2))
next
  case (3 N \<sigma>)
  thus ?case
    using assms(3)
    ..
next
  case (4 N e es \<sigma>)
  thus ?case
    by (intro assms(4))
qed

lemma (in path_search) path_search_fold'_induct_2:
  assumes "path_search_invar' N e \<sigma>"
  assumes
    "\<And>N e \<sigma>.
        path_search_fold'_dom (Inl (N, e, \<sigma>)) \<Longrightarrow> (tree_arc_2 e \<sigma> \<Longrightarrow> Q N (incidence_2 (multigraph \<sigma>) (head e)) \<sigma>) \<Longrightarrow> P N e \<sigma>"
  assumes "\<And>N \<sigma>. Q N [] \<sigma>"
  assumes
    "\<And>N e es \<sigma>.
        path_search_fold'_dom (Inr (N, e # es, \<sigma>)) \<Longrightarrow> P N e \<sigma> \<Longrightarrow> Q N es (path_search N e \<sigma>) \<Longrightarrow> Q N (e # es) \<sigma>"
  shows
    "Q N (incidence_2 (multigraph \<sigma>) (head e)) \<sigma>"
proof (rule path_search_fold'.pinduct(2)[where ?P = P], goal_cases)
  case 1
  show ?case
    using assms(1)
    by (intro path_search_invar.path_search_fold'_dom_Inr)
next
  case (2 N e \<sigma>)
  thus ?case
    by (intro assms(2))
next
  case (3 N \<sigma>)
  thus ?case
    using assms(3)
    ..
next
  case (4 N e es \<sigma>)
  thus ?case
    by (intro assms(4))
qed

lemmas (in path_search) path_search_fold'_induct = path_search_fold'_induct_1 path_search_fold'_induct_2

(* FIXME: Prove the two induction rules separately. *)
(*
lemma (in path_search) path_search_fold'_induct:
  assumes "path_search_invar' N e \<sigma>"
  assumes
    "\<And>N e \<sigma>.
        (tree_arc_2 e \<sigma> \<Longrightarrow> Q N (incidence_2 (multigraph \<sigma>) (head e)) \<sigma>) \<Longrightarrow> P N e \<sigma>"
  assumes "\<And>N \<sigma>. Q N [] \<sigma>"
  assumes
    "\<And>N e es \<sigma>.
        P N e \<sigma> \<Longrightarrow> Q N es (path_search N e \<sigma>) \<Longrightarrow> Q N (e # es) \<sigma>"
  shows
    "P N e \<sigma>"
    "Q N (incidence_2 (multigraph \<sigma>) (head e)) \<sigma>"
  thm path_search_fold'.pinduct
proof -
  show "P N e \<sigma>"
  proof (rule path_search_fold'.pinduct[where ?Q = Q], goal_cases)
    case 1
    show ?case
      using assms(1)
      by (intro path_search_invar.path_search_fold'_dom_Inl)
  next
    case (2 N e \<sigma>)
    thus ?case
      by (intro assms(2))
  next
    case (3 N \<sigma>)
    thus ?case
      using assms(3)
      ..
  next
    case (4 N e es \<sigma>)
    thus ?case
      by (intro assms(4))
  qed
  show "Q N (incidence_2 (multigraph \<sigma>) (head e)) \<sigma>"
  proof (rule path_search_fold'.pinduct[where ?P = P], goal_cases)
    case 1
    show ?case
      using assms(1)
      by (intro path_search_invar.path_search_fold'_dom_Inr)
  next
    case (2 N e \<sigma>)
    thus ?case
      by (intro assms(2))
  next
    case (3 N \<sigma>)
    thus ?case
      using assms(3)
      ..
  next
    case (4 N e es \<sigma>)
    thus ?case
      by (intro assms(4))
  qed
  thm path_search_fold'.pinduct
qed
*)

subsubsection \<open>Correctness\<close>

lemma (in path_search) root_path_search_fold':
  shows
    "path_search_fold'_dom (Inl (N, e, \<sigma>)) \<Longrightarrow> root (path_search N e \<sigma>) = root \<sigma>"
    "path_search_fold'_dom (Inr (N, incidence_2 (multigraph \<sigma>) (head e), \<sigma>)) \<Longrightarrow>
     root (fold' N (incidence_2 (multigraph \<sigma>) (head e)) \<sigma>) = root \<sigma>"
proof (induction rule: path_search_fold'.pinduct)
  case (1 N e \<sigma>)
  thus ?case
    by (simp add: path_search.psimps Let_def root_algorithm_6 root_algorithm_5)
next
  case (2 N \<sigma>)
  thus ?case
    by (simp add: fold'.psimps(1))
next
  case (3 N e es \<sigma>)
  thus ?case
    by (simp add: fold'.psimps(2))
qed

lemma (in path_search)
  assumes "path_search_invar' N e \<sigma>"
  shows
    "root (path_search N e \<sigma>) = root \<sigma>"
    "root (fold' N (incidence_2 (multigraph \<sigma>) (head e)) \<sigma>) = root \<sigma>"
  using assms
  by (fast dest: path_search_invar.path_search_fold'_dom_Inl path_search_invar.path_search_fold'_dom_Inr root_path_search_fold')+

end