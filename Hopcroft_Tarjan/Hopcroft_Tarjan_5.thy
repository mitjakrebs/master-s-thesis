theory Hopcroft_Tarjan_5
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
  "tree_arc_2 \<sigma> \<equiv> tree.tree_arc (T_lookup (tree \<sigma>))"

definition lookup where
  "lookup \<sigma> v \<equiv> case T_lookup (tree \<sigma>) v of None \<Rightarrow> None | Some p \<Rightarrow> Some (to_edge v p)"

definition incidence_2 where
  "incidence_2 \<sigma> \<equiv> Directed_Multigraph.incidence (\<lambda>v. incidence v (multigraph \<sigma>))"

function (domintros) path_search where
  "path_search N e \<sigma> =
   (if tree_arc_2 \<sigma> e
    then if incidence_2 \<sigma> (head e) = []
         then let \<sigma>1 = \<sigma>\<lparr>ESTACK := e # ESTACK \<sigma>\<rparr>;
                  \<sigma>2 = algorithm_5 N e \<sigma>1;
                  \<sigma>3 = algorithm_6 N e \<sigma>2
              in case lookup \<sigma>3 (tail e) of
                   None \<Rightarrow> \<sigma>3 |
                   Some e' \<Rightarrow> path_search N e' \<sigma>3
         else path_search N (hd (incidence_2 \<sigma> (head e))) \<sigma>
    else let \<sigma>1 = \<sigma>\<lparr>ESTACK := e # ESTACK \<sigma>\<rparr>
         in case lookup \<sigma>1 (tail e) of
                   None \<Rightarrow> \<sigma>1 |
                   Some e' \<Rightarrow> path_search N e' \<sigma>1)"
  by auto
thm path_search.pinduct

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

sublocale steps_1_2_3_high_3
  where N = "N G r"
    and I = "\<lambda>v. incidence v (I G r)"
    and G = "P.E G"
    and T = "T_lookup (T G r)"
  using biconnected_multigraph r_mem_V
  by (intro steps_1_2_3_high_3)

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

definition (in path_search) current_multigraph :: "('b, 't, 'g, 'a) state \<Rightarrow> ('a, 'b) Directed_Multigraph.multigraph" where
  "current_multigraph \<sigma> \<equiv> P.A (multigraph \<sigma>) \<union> set (ESTACK \<sigma>)"

locale path_search_invar = path_search_valid_input
  where T_update = T_update
    and insert = insert
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g" +
  fixes \<sigma> :: "('b, 't, 'g, 'a) state"
    (* QUESTION: Use P.E instead? *)
  assumes finite_current_multigraph: "finite (undirect ` current_multigraph \<sigma>)"
  assumes simple_current_multigraph: "simple (undirect ` current_multigraph \<sigma>)"
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
  shows "path_search_invar'' (init r T P)"
  sorry

lemma (in path_search_invar) finite_multigraph_Cs:
  shows "Ball (set (map set (map (map undirect) (Cs \<sigma>)))) (Multigraph.finite_multigraph other)"
  sorry

subsubsection \<open>Termination\<close>

lemma (in path_search_valid_input) path_search_dom:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_dom (N, e, \<sigma>)"
  sorry

lemma (in path_search_invar) path_search_dom:
  shows "path_search_dom (N, e, \<sigma>)"
  using path_search_invar_axioms
  by (intro path_search_dom)

lemma (in path_search) path_search_simps:
  assumes "path_search_invar' N e \<sigma>"
  shows
    "path_search N e \<sigma> =
     (if tree_arc_2 \<sigma> e
      then if incidence_2 \<sigma> (head e) = []
           then let \<sigma>1 = \<sigma>\<lparr>ESTACK := e # ESTACK \<sigma>\<rparr>;
                    \<sigma>2 = algorithm_5 N e \<sigma>1;
                    \<sigma>3 = algorithm_6 N e \<sigma>2
                in case lookup \<sigma>3 (tail e) of
                     None \<Rightarrow> \<sigma>3 |
                     Some e' \<Rightarrow> path_search N e' \<sigma>3
           else path_search N (hd (incidence_2 \<sigma> (head e))) \<sigma>
      else let \<sigma>1 = \<sigma>\<lparr>ESTACK := e # ESTACK \<sigma>\<rparr>
           in case lookup \<sigma>1 (tail e) of
                None \<Rightarrow> \<sigma>1 |
                Some e' \<Rightarrow> path_search N e' \<sigma>1)"
  using assms
  by (intro path_search_invar.path_search_dom path_search.psimps)

lemma (in path_search) path_search_induct:
  assumes "path_search_invar' N e \<sigma>"
  assumes
    "\<And>N e \<sigma>.
        (\<And>\<sigma>3 e'.
            tree_arc_2 \<sigma> e \<Longrightarrow>
            incidence_2 \<sigma> (head e) = [] \<Longrightarrow>
            \<sigma>3 = algorithm_6 N e (algorithm_5 N e (\<sigma>\<lparr>ESTACK := e # ESTACK \<sigma>\<rparr>)) \<Longrightarrow>
            lookup \<sigma>3 (tail e) = Some e' \<Longrightarrow>
            P N e' \<sigma>3) \<Longrightarrow>
        (tree_arc_2 \<sigma> e \<Longrightarrow> incidence_2 \<sigma> (head e) \<noteq> [] \<Longrightarrow> P N (hd (incidence_2 \<sigma> (head e))) \<sigma>) \<Longrightarrow>
        (\<And>\<sigma>1 e'.
            \<not> tree_arc_2 \<sigma> e \<Longrightarrow>
            \<sigma>1 = \<sigma>\<lparr>ESTACK := e # ESTACK \<sigma>\<rparr> \<Longrightarrow>
            lookup \<sigma>1 (tail e) = Some e' \<Longrightarrow>
            P N e' \<sigma>1) \<Longrightarrow>
        P N e \<sigma>"
  shows "P N e \<sigma>"
  using assms
  by (blast intro: path_search_invar.path_search_dom path_search.pinduct)

subsubsection \<open>Correctness\<close>

lemma (in path_search_valid_input) is_split_tbd_path_search:
  assumes "path_search_invar'' \<sigma>"
  shows
    "is_split_tbd
      (undirect ` current_multigraph \<sigma> # map set (map (map undirect) (Cs \<sigma>)))
      (undirect ` current_multigraph (path_search N e \<sigma>) # map set (map (map undirect) (Cs (path_search N e \<sigma>))))"
  using assms
proof (induct rule: path_search_induct[OF assms])
  case (1 N e \<sigma>)
  then show ?case sorry
qed

lemma (in path_search_valid_input) no_separation_pair_path_search:
  assumes "path_search_invar'' \<sigma>"
  assumes "is_separation_pair (undirect ` current_multigraph (path_search N e \<sigma>)) a b"
  shows
    "a \<notin> tree.D (T_lookup (tree (path_search N e \<sigma>))) (tail e) \<or>
     b \<notin> tree.D (T_lookup (tree (path_search N e \<sigma>))) (tail e)"
  using assms
proof (induct rule: path_search_induct[OF assms(1)])
  case (1 N e \<sigma>)
  then show ?case sorry
qed

(* TODO: Move. *)
lemma (in path_search) edges_from_fun_incidence_eq_A:
  shows "edges_from_fun (\<lambda>v. incidence v P) = P.A P"
  by (force simp add: edges_from_fun_def incidence_def to_edge_def P.A_def)

(* TODO: Move. *)
lemma (in algorithm_3_valid_input) image_undirect_A_eq_E:
  shows "undirect ` P.A (I G r) = P.E G"
  using undirect_P_eq_G
  by (force simp add: edges_from_fun_incidence_eq_A)

lemma (in algorithm_3_pre_valid_input) algorithm_3_correct:
  shows "are_split_components (undirect ` P.A P) (map set (map (map undirect) (algorithm_3 r T P N)))"
  unfolding algorithm_3_def Let_def
proof (intro are_split_componentsI_2, goal_cases)
  case 1
  let ?\<sigma> = "path_search N (hd (Directed_Multigraph.incidence (\<lambda>v. incidence v P) r)) (init r T P)"
  have "Multigraph.finite_multigraph other (undirect ` set (ESTACK ?\<sigma>))"
    sorry
  moreover have "Ball (set (map set (map (map undirect) (Cs ?\<sigma>)))) (Multigraph.finite_multigraph other)"
    sorry
  ultimately show ?case
    by fastforce
next
  case 2
  show ?case
    thm is_split_tbd_path_search[OF path_search_invar_init]
    sorry
next
  case 3
  let ?\<sigma> = "path_search N (hd (Directed_Multigraph.incidence (\<lambda>v. incidence v P) r)) (init r T P)"
  show ?case sorry
qed

lemma (in algorithm_3_valid_input) algorithm_3'_correct:
  shows "are_split_components (P.E G) (map set (algorithm_3' G r))"
  unfolding image_undirect_A_eq_E[symmetric] algorithm_3'_def
  using algorithm_3_correct
  .

end