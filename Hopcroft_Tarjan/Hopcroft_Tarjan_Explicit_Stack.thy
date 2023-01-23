theory Hopcroft_Tarjan_Explicit_Stack
  imports
    Hopcroft_Tarjan
begin

type_synonym ('a, 'b) component = "('a, 'b) Directed_Multigraph.edge list"

record ('b, 't, 'g, 'a) state =
  root :: 'b
  tree :: 't
  multigraph :: 'g
  stack :: "('a, 'b) Directed_Multigraph.edge list"
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

definition DONE where
  "DONE \<sigma> \<equiv> stack \<sigma> = []"

(* FIXME: This specification is not correct! *)
function (domintros) path_search where
  "path_search N \<sigma> =
   (if \<not> DONE \<sigma>
    then let e = hd (stack \<sigma>);
             \<sigma>1 = \<sigma>\<lparr>stack := tl (stack \<sigma>)\<rparr>
         in if tree_arc_2 e \<sigma>1
            then let \<sigma>2 = path_search N (\<sigma>1\<lparr>stack := incidence_2 (multigraph \<sigma>1) (head e) @ stack \<sigma>1\<rparr>);
                     \<sigma>3 = \<sigma>2\<lparr>ESTACK := e # ESTACK \<sigma>2\<rparr>;
                     \<sigma>4 = algorithm_5 N e \<sigma>3;
                     \<sigma>5 = algorithm_6 N e \<sigma>4
                 in \<sigma>5
            else \<sigma>1\<lparr>ESTACK := e # ESTACK \<sigma>1\<rparr>
    else \<sigma>)"
  by pat_completeness simp
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
    stack = Directed_Multigraph.incidence (\<lambda>v. incidence v P) r,
    ESTACK = [],
    Cs = []\<rparr>"

definition algorithm_3 where
  "algorithm_3 r T P N \<equiv>
   let \<sigma> = path_search N (init r T P)
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
  assumes "0 \<le> N v"
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
  "path_search_invar' N \<equiv>
   path_search_invar
    empty delete incidence invar
    other
    T_empty T_delete T_lookup T_invar
    algorithm_5
    algorithm_6
    N
    T_update
    insert"

abbreviation (in path_search_valid_input) path_search_invar'' where
  "path_search_invar'' \<equiv> path_search_invar' N"

lemma (in algorithm_3_pre_valid_input) path_search_invar_init:
  shows "path_search_invar' N (init r T P)"
  sorry

subsubsection \<open>Termination\<close>

lemma (in path_search_valid_input) path_search_dom:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_dom (N, \<sigma>)"
  sorry

lemma (in path_search_invar) path_search_dom:
  shows "path_search_dom (N, \<sigma>)"
  using path_search_invar_axioms
  by (intro path_search_dom)

lemma (in path_search) path_search_simps:
  assumes "path_search_invar' N \<sigma>"
  shows
    "path_search N \<sigma> =
     (if \<not> DONE \<sigma>
      then let e = hd (stack \<sigma>);
               \<sigma>1 = \<sigma>\<lparr>stack := tl (stack \<sigma>)\<rparr>
           in if tree_arc_2 e \<sigma>1
              then let \<sigma>2 = path_search N (\<sigma>1\<lparr>stack := incidence_2 (multigraph \<sigma>1) (head e) @ stack \<sigma>1\<rparr>);
                       \<sigma>3 = \<sigma>2\<lparr>ESTACK := e # ESTACK \<sigma>2\<rparr>;
                       \<sigma>4 = algorithm_5 N e \<sigma>3;
                       \<sigma>5 = algorithm_6 N e \<sigma>4
                   in \<sigma>5
              else \<sigma>1\<lparr>ESTACK := e # ESTACK \<sigma>1\<rparr>
      else \<sigma>)"
  using assms
  by (intro path_search_invar.path_search_dom path_search.psimps)

lemma (in path_search) path_search_induct:
  assumes "path_search_invar' N \<sigma>"
  assumes
    "\<And>N \<sigma>.
        (\<And>e \<sigma>1.
            \<not> DONE \<sigma> \<Longrightarrow>
            e = hd (stack \<sigma>) \<Longrightarrow>
            \<sigma>1 = \<sigma>\<lparr>stack := tl (stack \<sigma>)\<rparr> \<Longrightarrow>
            tree_arc_2 e \<sigma>1 \<Longrightarrow> P N (\<sigma>1\<lparr>stack := incidence_2 (multigraph \<sigma>1) (head e) @ stack \<sigma>1\<rparr>)) \<Longrightarrow>
        P N \<sigma>"
  shows "P N \<sigma>"
  using assms
  by (blast intro: path_search_invar.path_search_dom path_search.pinduct)

subsubsection \<open>Correctness\<close>

lemma (in path_search_valid_input) root_path_search:
  assumes "path_search_invar'' \<sigma>"
  shows "root (path_search N \<sigma>) = root \<sigma>"
  using assms
proof (induct rule: path_search_induct[OF assms])
  case (1 N \<sigma>)
  then show ?case sorry
qed

end