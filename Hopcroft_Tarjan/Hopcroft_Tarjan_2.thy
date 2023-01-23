theory Hopcroft_Tarjan_2
  imports
    Hopcroft_Tarjan
begin

subsection \<open>Specification of the algorithm\<close>

(* TODO: Rename. *)
datatype 'b T = EOS | Triple (h': nat) (a': 'b) (b': 'b)

type_synonym ('a, 'b) component = "('a, 'b) Directed_Multigraph.edge list"

(* TODO: Add DEGREE. *)
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
  assumes tree_while_loop_1: "tree (while_loop_1 \<sigma>) = tree \<sigma>"
  assumes multigraph_while_loop_1: "multigraph (while_loop_1 \<sigma>) = multigraph \<sigma>"
  assumes F_while_loop_1: "F (while_loop_1 \<sigma>) = F \<sigma>"
  assumes ESTACK_while_loop_1: "ESTACK (while_loop_1 \<sigma>) = ESTACK \<sigma>"
  assumes Cs_while_loop_1: "Cs (while_loop_1 \<sigma>) = Cs \<sigma>"
  assumes root_while_loop_2: "root (while_loop_2 \<sigma>) = root \<sigma>"
  assumes tree_while_loop_2: "tree (while_loop_2 \<sigma>) = tree \<sigma>"
  assumes multigraph_while_loop_2: "multigraph (while_loop_2 \<sigma>) = multigraph \<sigma>"
  assumes F_while_loop_2: "F (while_loop_2 \<sigma>) = F \<sigma>"
  assumes ESTACK_while_loop_2: "ESTACK (while_loop_2 \<sigma>) = ESTACK \<sigma>"
  assumes Cs_while_loop_2: "Cs (while_loop_2 \<sigma>) = Cs \<sigma>"
  assumes root_while_loop_3: "root (while_loop_3 \<sigma>) = root \<sigma>"
  assumes tree_while_loop_3: "tree (while_loop_3 \<sigma>) = tree \<sigma>"
  assumes multigraph_while_loop_3: "multigraph (while_loop_3 \<sigma>) = multigraph \<sigma>"
  assumes F_while_loop_3: "F (while_loop_3 \<sigma>) = F \<sigma>"
  assumes ESTACK_while_loop_3: "ESTACK (while_loop_3 \<sigma>) = ESTACK \<sigma>"
  assumes Cs_while_loop_3: "Cs (while_loop_3 \<sigma>) = Cs \<sigma>"
  assumes root_while_loop_4: "root (while_loop_4 \<sigma>) = root \<sigma>"
  assumes tree_while_loop_4: "tree (while_loop_4 \<sigma>) = tree \<sigma>"
  assumes multigraph_while_loop_4: "multigraph (while_loop_4 \<sigma>) = multigraph \<sigma>"
  assumes F_while_loop_4: "F (while_loop_4 \<sigma>) = F \<sigma>"
  assumes ESTACK_while_loop_4: "ESTACK (while_loop_4 \<sigma>) = ESTACK \<sigma>"
  assumes Cs_while_loop_4: "Cs (while_loop_4 \<sigma>) = Cs \<sigma>"
  assumes root_algorithm_5: "root (algorithm_5 \<sigma>) = root \<sigma>"
  assumes root_algorithm_6: "root (algorithm_6 \<sigma>) = root \<sigma>"
  assumes TSTACK_algorithm_6: "TSTACK (algorithm_6 \<sigma>) = TSTACK \<sigma>"
begin

definition tree_arc_2 :: "('a, 'b) Directed_Multigraph.edge \<Rightarrow> ('b, 't, 'g, 'm, 'a) state \<Rightarrow> bool" where
  "tree_arc_2 e \<sigma> \<equiv> tree.tree_arc (T_lookup (tree \<sigma>)) e"

(*
definition traverse_tree_arc ::
  "('b \<Rightarrow> nat)
   \<Rightarrow> ('b \<Rightarrow> 'b)
      \<Rightarrow> ('b \<Rightarrow> 'b)
         \<Rightarrow> ('b \<Rightarrow> nat)
            \<Rightarrow> (('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool)
               \<Rightarrow> ('a, 'b) Directed_Multigraph.edge
                  \<Rightarrow> ('b, 't, 'g, 'm, 'a) state
                     \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "traverse_tree_arc N lowpt1 lowpt2 ND START e \<sigma> \<equiv> \<sigma>"
*)

(*
definition traverse_frond ::
  "('b \<Rightarrow> nat)
   \<Rightarrow> ('b \<Rightarrow> 'b)
      \<Rightarrow> ('b \<Rightarrow> 'b)
         \<Rightarrow> ('b \<Rightarrow> nat)
            \<Rightarrow> (('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool)
               \<Rightarrow> ('a, 'b) Directed_Multigraph.edge
                  \<Rightarrow> ('b, 't, 'g, 'm, 'a) state
                     \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "traverse_frond N lowpt1 lowpt2 ND START e \<sigma> \<equiv> \<sigma>"
*)

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
  "traverse_edge N lowpt1 lowpt2 ND START e \<sigma> \<equiv>
   if tree_arc e \<sigma> then traverse_tree_arc N lowpt1 lowpt2 ND START e \<sigma>
   else traverse_frond N lowpt1 lowpt2 ND START e \<sigma>"
*)

(* QUESTION: Create locale Directed_Incidence_Structure and move? *)
definition incidence_2 :: "'g \<Rightarrow> 'b \<Rightarrow> ('a, 'b) Directed_Multigraph.edge list" where
  "incidence_2 G \<equiv> Directed_Multigraph.incidence (\<lambda>v. incidence v G)"

(*
function (domintros) path_search and traverse_edge where
  "traverse_edge N lowpt1 lowpt2 ND START e \<sigma> =
   (if tree_arc e \<sigma>
    then let \<sigma>1 = if START e then while_loop_1 \<sigma> else \<sigma>;
             \<sigma>2 = path_search N lowpt1 lowpt2 ND START (head e) \<sigma>1;
             \<sigma>3 = \<sigma>2\<lparr>ESTACK := e # ESTACK \<sigma>2\<rparr>;
             \<sigma>4 = algorithm_5 \<sigma>3;
             \<sigma>5 = algorithm_6 \<sigma>4;
             \<sigma>6 = if START e then while_loop_2 \<sigma>5 else \<sigma>5;
             \<sigma>7 = while_loop_3 \<sigma>6
         in \<sigma>7
    else let \<sigma>8 = if START e then while_loop_4 \<sigma> else \<sigma>;
             \<sigma>9 = \<sigma>8\<lparr>ESTACK := e # ESTACK \<sigma>8\<rparr>
         in \<sigma>9)" |
  "path_search N lowpt1 lowpt2 ND START v \<sigma> =
   fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>"
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
  "path_search N lowpt1 lowpt2 ND START v \<sigma> =
   fold
    (\<lambda>e \<sigma>. if tree_arc_2 e \<sigma>
           then let \<sigma>1 = if START e then while_loop_1 \<sigma> else \<sigma>;
                    \<sigma>2 = path_search N lowpt1 lowpt2 ND START (head e) \<sigma>1;
                    \<sigma>3 = \<sigma>2\<lparr>ESTACK := e # ESTACK \<sigma>2\<rparr>;
                    \<sigma>4 = algorithm_5 \<sigma>3;
                    \<sigma>5 = algorithm_6 \<sigma>4;
                    \<sigma>6 = if START e then while_loop_2 \<sigma>5 else \<sigma>5;
                    \<sigma>7 = while_loop_3 \<sigma>6
                in \<sigma>7
           else let \<sigma>8 = if START e then while_loop_4 \<sigma> else \<sigma>;
                    \<sigma>9 = \<sigma>8\<lparr>ESTACK := e # ESTACK \<sigma>8\<rparr>
                in \<sigma>9)
    (incidence_2 (multigraph \<sigma>) v)
    \<sigma>"
  by auto
thm path_search.pinduct

definition traverse_tree_arc where
  "traverse_tree_arc N lowpt1 lowpt2 ND START e \<sigma> \<equiv>
   let \<sigma>1 = if START e then while_loop_1 \<sigma> else \<sigma>;
       \<sigma>2 = path_search N lowpt1 lowpt2 ND START (head e) \<sigma>1;
       \<sigma>3 = \<sigma>2\<lparr>ESTACK := e # ESTACK \<sigma>2\<rparr>;
       \<sigma>4 = algorithm_5 \<sigma>3;
       \<sigma>5 = algorithm_6 \<sigma>4;
       \<sigma>6 = if START e then while_loop_2 \<sigma>5 else \<sigma>5;
       \<sigma>7 = while_loop_3 \<sigma>6
   in \<sigma>7"

definition traverse_frond where
  "traverse_frond N lowpt1 lowpt2 ND START e \<sigma> \<equiv>
   let \<sigma>8 = if START e then while_loop_4 \<sigma> else \<sigma>;
       \<sigma>9 = \<sigma>8\<lparr>ESTACK := e # ESTACK \<sigma>8\<rparr>
   in \<sigma>9"

definition traverse_edge where
  "traverse_edge N lowpt1 lowpt2 ND START e \<sigma> \<equiv>
   if tree_arc_2 e \<sigma> then traverse_tree_arc N lowpt1 lowpt2 ND START e \<sigma>
   else traverse_frond N lowpt1 lowpt2 ND START e \<sigma>"

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
  "path_search N lowpt1 lowpt2 ND START v \<sigma> \<equiv>
   fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>"
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
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  fixes N :: "'b \<Rightarrow> nat"
  fixes lowpt1 :: "'b \<Rightarrow> 'b"
  fixes lowpt2 :: "'b \<Rightarrow> 'b"
  fixes ND :: "'b \<Rightarrow> nat"
  fixes START :: "('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool"
  fixes v :: 'b
begin

abbreviation path_search' :: "('b, 't, 'g, 'm, 'a) state \<Rightarrow> ('b, 't, 'g, 'm, 'a) state" where
  "path_search' \<equiv> path_search N lowpt1 lowpt2 ND START v"

abbreviation traverse_edge' where
  "traverse_edge' \<equiv> traverse_edge N lowpt1 lowpt2 ND START"

abbreviation traverse_tree_arc' where
  "traverse_tree_arc' \<equiv> traverse_tree_arc N lowpt1 lowpt2 ND START"

abbreviation traverse_frond' where
  "traverse_frond' \<equiv> traverse_frond N lowpt1 lowpt2 ND START"

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
  assumes steps_1_2_3_high_2: "steps_1_2_3_high_2 r (\<lambda>v. incidence v P) (T_lookup T) N"
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
    and ND = "ND r T P"
    and START = "START r T P"
  ..
*)

end

abbreviation (in algorithm_3_pre) algorithm_3_pre_valid_input' :: "'b \<Rightarrow> 't \<Rightarrow> 'g \<Rightarrow> ('b \<Rightarrow> nat) \<Rightarrow> bool" where
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

(* TODO: Move. *)
lemma (in path_search) edges_from_fun_incidence_eq_A:
  shows "edges_from_fun (\<lambda>v. incidence v P) = P.A P"
  by (force simp add: edges_from_fun_def incidence_def to_edge_def P.A_def)

(* TODO: Move. *)
lemma (in algorithm_3_valid_input) image_undirect_A_eq_E:
  shows "undirect ` P.A (I G r) = P.E G"
  using undirect_P_eq_G
  by (force simp add: edges_from_fun_incidence_eq_A)

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
  assumes palm_tree_2: "palm_tree_2 (root \<sigma>) (T_lookup (tree \<sigma>)) (\<lambda>v. incidence v (multigraph \<sigma>))"
begin

abbreviation \<sigma>' :: "('b, 't, 'g, 'm, 'a) state" where
  "\<sigma>' \<equiv> path_search' \<sigma>"

(*
sublocale palm_tree_2
  where r = "root \<sigma>"
    and T = "T_lookup (tree \<sigma>)"
    and I = "\<lambda>v. incidence v (multigraph \<sigma>)"
  using palm_tree_2
  .
*)

sublocale steps_1_2_3_high_3
  where r = "root \<sigma>"
    and T = "T_lookup (tree \<sigma>)"
    and I = "\<lambda>v. incidence v (multigraph \<sigma>)"
    and G = "undirect ` P.A (multigraph \<sigma>)"
  sorry

lemmas mem_D_iff_tree_path = mem_D_iff_tree_path
lemmas tree_path_if_tree_arc' = tree_path_if_tree_arc'
lemmas tree_path_trans = tree_path_trans
lemmas is_type_1_pair'_def = is_type_1_pair'_def
lemmas is_type_1_pair_iff = is_type_1_pair_iff
lemmas lemma_7 = lemma_7

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
  assumes e_mem_set_incidence_2: "e \<in> set (incidence_2 (multigraph \<sigma>) v)"

locale traverse_edge_invar_tree_arc = traverse_edge_invar
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes tree_arc: "tree_arc_2 e \<sigma>"

locale traverse_edge_invar_frond = traverse_edge_invar
  where T_update = T_update
    and insert = insert
    and F_update = F_update
  for T_update :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 't \<Rightarrow> 't"
    and insert :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
    and F_update :: "'b \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm" +
  assumes frond: "\<not> tree_arc_2 e \<sigma>"

(* FIXME: *)
abbreviation (in path_search) path_search_invar' ::
  "('b \<Rightarrow> nat)
   \<Rightarrow> ('b \<Rightarrow> 'b)
      \<Rightarrow> ('b \<Rightarrow> 'b)
         \<Rightarrow> ('b \<Rightarrow> nat)
            \<Rightarrow> (('a, 'b) Directed_Multigraph.edge \<Rightarrow> bool)
               \<Rightarrow> 'b
                  \<Rightarrow> ('b, 't, 'g, 'm, 'a) state
                     \<Rightarrow> bool" where
  "path_search_invar' N lowpt1 lowpt2 ND START v \<equiv>
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
  "path_search_invar'' \<equiv> path_search_invar' N lowpt1 lowpt2 ND START v"

(*
context algorithm_3_pre_valid_input
begin
sublocale path_search_invar
  where lowpt1 = "lowpt1 r T P N"
    and lowpt2 = "lowpt2 r T P N"
    and ND = "ND r T P"
    and START = "START r T P"
    and v = r
    and \<sigma> = "init r T P"
  sorry
end
*)

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
  shows "ESTACK \<sigma>' = map (to_edge v) (tree_of_2.flatten (T_lookup (tree \<sigma>')) (\<lambda>v. incidence v (multigraph \<sigma>')) v) @ ESTACK \<sigma>"
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

lemma (in path_search_invar) path_search_invar_fold:
  shows "path_search_invar'' (fold traverse_edge' (incidence_2 (multigraph \<sigma>) v) \<sigma>)"
  sorry

(* FIXME: *)
lemma (in path_search_invar) path_search_invar_\<sigma>':
  shows "path_search_invar'' \<sigma>'"
  sorry

subsubsection \<open>Termination\<close>

lemma (in path_search_valid_input) path_search_dom:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_dom (N, lowpt1, lowpt2, ND, START, v, \<sigma>)"
  sorry

lemma (in path_search_invar) path_search_dom:
  shows "path_search_dom (N, lowpt1, lowpt2, ND, START, v, \<sigma>)"
  using path_search_invar_axioms
  by (intro path_search_dom)

lemma (in path_search) path_search_simps:
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  shows
    "path_search N lowpt1 lowpt2 ND START v \<sigma> =
     fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>"
  unfolding traverse_edge_def traverse_tree_arc_def traverse_frond_def
  using assms
  by (intro path_search_invar.path_search_dom path_search.psimps)

(*
lemma (in path_search_valid_input) path_search_traverse_edge_dom_Inl:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_traverse_edge_dom (Inl (N, lowpt1, lowpt2, ND, START, v, \<sigma>))"
  sorry

lemma (in path_search_valid_input) path_search_traverse_edge_dom_Inr:
  assumes "path_search_invar'' \<sigma>"
  shows "path_search_traverse_edge_dom (Inr (N, lowpt1, lowpt2, ND, START, e, \<sigma>))"
  sorry

lemma (in path_search_invar) path_search_traverse_edge_dom_Inl:
  shows "path_search_traverse_edge_dom (Inl (N, lowpt1, lowpt2, ND, START, v, \<sigma>))"
  sorry

lemma (in path_search_invar) path_search_traverse_edge_dom_Inr:
  shows "path_search_traverse_edge_dom (Inr (N, lowpt1, lowpt2, ND, START, e, \<sigma>))"
  sorry
*)

(*
lemma (in path_search) path_search_traverse_edge_induct:
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  assumes
    "\<And>N lowpt1 lowpt2 ND START e \<sigma>.
        (tree_arc e \<sigma> \<Longrightarrow> P N lowpt1 lowpt2 ND START (head e) (if START e then while_loop_1 \<sigma> else \<sigma>)) \<Longrightarrow>
        Q N lowpt1 lowpt2 ND START e \<sigma>"
  assumes
    "\<And>N lowpt1 lowpt2 ND START v \<sigma>.
        (\<And>e \<sigma>'. e \<in> set (incidence_2 (multigraph \<sigma>) v) \<Longrightarrow> Q N lowpt1 lowpt2 ND START e \<sigma>') \<Longrightarrow>
        P N lowpt1 lowpt2 ND START v \<sigma>"
  shows
    "P N lowpt1 lowpt2 ND START v \<sigma>"
    "Q N lowpt1 lowpt2 ND START e \<sigma>"
proof -
  show "P N lowpt1 lowpt2 ND START v \<sigma>"
  proof (rule path_search_traverse_edge.pinduct[of N lowpt1 lowpt2 ND START, where ?Q = Q], goal_cases)
    case 1
    then show ?case
      using assms(1)
      by (intro path_search_invar.path_search_traverse_edge_dom_Inl)
  next
    case (2 N lowpt1 lowpt2 ND START e \<sigma>)
    thus ?case
      by (intro assms(2)) simp
  next
    case (3 N lowpt1 lowpt2 ND START v \<sigma>)
    thus ?case
      by (intro assms(3))
  qed
  show "Q N lowpt1 lowpt2 ND START e \<sigma>"
  proof (rule path_search_traverse_edge.pinduct[of N lowpt1 lowpt2 ND START, where ?P = P], goal_cases)
    case 1
    then show ?case
      using assms(1)
      by (intro path_search_invar.path_search_traverse_edge_dom_Inr)
  next
    case (2 N lowpt1 lowpt2 ND START e \<sigma>)
    thus ?case
      by (intro assms(2)) simp
  next
    case (3 N lowpt1 lowpt2 ND START v \<sigma>)
    thus ?case
      by (intro assms(3))
  qed
qed
*)

lemma (in path_search) path_search_induct:
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  assumes
    "\<And>N lowpt1 lowpt2 ND START v \<sigma>.
        (\<And>e \<sigma>'.
            e \<in> set (incidence_2 (multigraph \<sigma>) v) \<Longrightarrow>
            tree_arc_2 e \<sigma>' \<Longrightarrow>
            P N lowpt1 lowpt2 ND START (head e) (if START e then while_loop_1 \<sigma>' else \<sigma>')) \<Longrightarrow>
        P N lowpt1 lowpt2 ND START v \<sigma>"
  shows "P N lowpt1 lowpt2 ND START v \<sigma>"
    (* TODO: Remove of part. *)
proof (rule path_search.pinduct[of N lowpt1 lowpt2 ND START v \<sigma>], goal_cases)
  case 1
  show ?case
    using assms(1)
    by (intro path_search_invar.path_search_dom)
next
  case (2 N lowpt1 lowpt2 ND START v \<sigma>)
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
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  shows
    "root (path_search N lowpt1 lowpt2 ND START v \<sigma>) = root \<sigma>"
    "root (traverse_edge N lowpt1 lowpt2 ND START e \<sigma>) = root \<sigma>"
  using assms
  thm path_search_traverse_edge_induct[OF assms, of _ _ N lowpt1 lowpt2 ND START]
proof (induct rule: path_search_traverse_edge_induct[OF assms, of _ _ N lowpt1 lowpt2 ND START])
  case (1 N lowpt1 lowpt2 ND START e \<sigma>)
  then show ?case sorry
next
  case (2 N lowpt1 lowpt2 ND START v \<sigma>)
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
    "tree_arc_2 e \<sigma> \<Longrightarrow>
     root (path_search N lowpt1 lowpt2 ND START (head e) (if START e then while_loop_1 \<sigma> else \<sigma>)) =
     root (if START e then while_loop_1 \<sigma> else \<sigma>)"
  shows "root (traverse_edge N lowpt1 lowpt2 ND START e \<sigma>) = root \<sigma>"
proof (cases "tree_arc_2 e \<sigma>")
  case True
  hence
    "root (traverse_edge N lowpt1 lowpt2 ND START e \<sigma>) =
     root (path_search N lowpt1 lowpt2 ND START (head e) (if START e then while_loop_1 \<sigma> else \<sigma>))"
    by (simp add: traverse_edge_def traverse_tree_arc_def Let_def root_while_loop_3 root_while_loop_2 root_algorithm_6 root_algorithm_5)
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
    by (simp add: traverse_edge_def traverse_frond_def Let_def)
qed

lemma (in path_search) root_path_search_aux:
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  assumes "e \<in> set (incidence_2 (multigraph \<sigma>) v)"
  assumes "tree_arc_2 e \<sigma>'"
  shows "path_search_invar' N lowpt1 lowpt2 ND START v (if START e then while_loop_1 \<sigma>' else \<sigma>')"
  sorry

lemma (in path_search) root_path_search:
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  shows "root (path_search N lowpt1 lowpt2 ND START v \<sigma>) = root \<sigma>"
  using assms
proof (induct rule: path_search_induct[OF assms, of _ N lowpt1 lowpt2 ND START v])
  case (1 N lowpt1 lowpt2 ND START v \<sigma>)
  have "root (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>) = root \<sigma>"
  proof -
    { fix e \<sigma>'
      assume "e \<in> set (incidence_2 (multigraph \<sigma>) v)"
      hence "root (traverse_edge N lowpt1 lowpt2 ND START e \<sigma>') = root \<sigma>'"
        using "1.prems"
        by (auto intro: root_path_search_aux "1.hyps" root_traverse_edge) }
    thus ?thesis
      by (intro root_fold)
  qed
  thm root_traverse_edge
  thm root_fold
  thus ?case
    using "1.prems"
    by (simp add: path_search_simps)
qed

(*
lemma (in path_search) idk_fold:
  shows "a \<notin> tree.D (T_lookup (tree (fold f l \<sigma>))) v \<or> b \<notin> tree.D (T_lookup (tree (fold f l \<sigma>))) v"
  sorry
*)

lemma (in path_search) idk_traverse_edge:
  shows
    "a \<notin> tree.D (T_lookup (tree (traverse_edge N lowpt1 lowpt2 ND START e \<sigma>))) (head e) \<or>
     b \<notin> tree.D (T_lookup (tree (traverse_edge N lowpt1 lowpt2 ND START e \<sigma>))) (head e)"
proof (cases "tree_arc_2 e \<sigma>")
  case True
  then show ?thesis sorry
next
  case False
  then show ?thesis sorry
qed

(* QQQ *)
lemma (in path_search) idk_aux_1:
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  assumes "N a < N b"
  assumes
    "steps_1_2_3_high.is_type_1_pair
      (\<lambda>x. incidence x (multigraph (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>)))
      (T_lookup (tree (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>))) N a b s t"
  shows
    "b \<notin> tree.D (T_lookup (tree (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>))) v \<or>
     s \<notin> tree.D (T_lookup (tree (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>))) v"
  using assms
proof (induct rule: path_search_induct[OF assms(1), of _ N lowpt1 lowpt2 ND START v])
  case (1 N lowpt1 lowpt2 ND START v \<sigma>)
  then show ?case sorry
qed

lemma (in path_search) idk_aux_2:
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  assumes "N a < N b"
  assumes
    "steps_1_2_3_high.is_type_2_pair'
      (\<lambda>x. incidence x (multigraph (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>)))
      (T_lookup (tree (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>))) N a b"
  shows
    "a \<notin> tree.D (T_lookup (tree (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>))) v \<or>
     b \<notin> tree.D (T_lookup (tree (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>))) v"
  using assms
proof (induct rule: path_search_induct[OF assms(1), of _ N lowpt1 lowpt2 ND START v])
  case (1 N lowpt1 lowpt2 ND START v \<sigma>)
  then show ?case sorry
qed

lemma (in path_search)
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  assumes "N a < N b"
  assumes "is_separation_pair (undirect ` P.A (multigraph (path_search N lowpt1 lowpt2 ND START v \<sigma>))) a b"
  shows
    "a \<notin> tree.D (T_lookup (tree (path_search N lowpt1 lowpt2 ND START v \<sigma>))) v \<or>
     b \<notin> tree.D (T_lookup (tree (path_search N lowpt1 lowpt2 ND START v \<sigma>))) v"
proof (rule ccontr, goal_cases)
  let ?\<sigma>' = "fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>"
  let ?I = "\<lambda>v. incidence v (multigraph ?\<sigma>')"
  let ?T = "T_lookup (tree ?\<sigma>')"
  let ?G = "undirect ` P.A (multigraph ?\<sigma>')"
  case 1
  hence
    assm: "a \<in> tree.D ?T v"
    "b \<in> tree.D ?T v"
    using assms(1)
    by (simp_all add: path_search_simps)
  consider
    "steps_1_2_3_high.is_type_1_pair' ?I ?T N a b" |
    "steps_1_2_3_high.is_type_2_pair' ?I ?T N a b" |
    "is_multiple_edge ?G {a, b} \<and> 4 \<le> card ?G"
    using assms(3)[unfolded path_search_simps[OF assms(1)]]
    by (auto simp add: path_search_invar.lemma_7[OF path_search_invar.path_search_invar_fold[OF assms(1)] assms(2)])
  thus ?case
  proof (cases)
    case 1
    then obtain s t where
      s_t: "steps_1_2_3_high.is_type_1_pair ?I ?T N a b s t"
      by (auto simp add: path_search_invar.is_type_1_pair'_def[OF path_search_invar.path_search_invar_fold[OF assms(1)]])
    hence "b \<notin> tree.D ?T v \<or> s \<notin> tree.D ?T v"
      using assms(1, 2)
      by (intro idk_aux_1)
    moreover have
      "s \<in> tree.D ?T v"
    proof -
      have
        "tree.tree_arc' ?T b s"
        using s_t
        by (simp add: path_search_invar.is_type_1_pair_iff[OF path_search_invar.path_search_invar_fold[OF assms(1)]])
      thus ?thesis
        using assm(2)
        by (auto simp add: path_search_invar.mem_D_iff_tree_path[OF path_search_invar.path_search_invar_fold[OF assms(1)]] dest: path_search_invar.tree_path_if_tree_arc'[OF path_search_invar.path_search_invar_fold[OF assms(1)]] path_search_invar.tree_path_trans[OF path_search_invar.path_search_invar_fold[OF assms(1)]])
    qed
    ultimately show ?thesis
      using assm(2)
      by fast
  next
    case 2
    hence "a \<notin> tree.D ?T v \<or> b \<notin> tree.D ?T v"
      using assms(1, 2)
      by (intro idk_aux_2)
    thus ?thesis
      using assm
      by blast
  next
    case 3
    then show ?thesis sorry
  qed
qed

lemma (in path_search)
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  assumes "is_separation_pair (undirect ` P.A (multigraph (path_search N lowpt1 lowpt2 ND START v \<sigma>))) a b"
  shows
    "a \<notin> tree.D (T_lookup (tree (path_search N lowpt1 lowpt2 ND START v \<sigma>))) v \<or>
     b \<notin> tree.D (T_lookup (tree (path_search N lowpt1 lowpt2 ND START v \<sigma>))) v"
  using assms
proof (induct rule: path_search_induct[OF assms(1), of _ N lowpt1 lowpt2 ND START v])
  case (1 N lowpt1 lowpt2 ND START v \<sigma>)
  have
    "a \<notin> tree.D (T_lookup (tree (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>))) v \<or>
     b \<notin> tree.D (T_lookup (tree (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>))) v"
  proof -
    { fix e \<sigma>'
      assume "e \<in> set (incidence_2 (multigraph \<sigma>) v)"
      hence
        "a \<notin> tree.D (T_lookup (tree (traverse_edge N lowpt1 lowpt2 ND START e \<sigma>'))) (head e) \<or>
         b \<notin> tree.D (T_lookup (tree (traverse_edge N lowpt1 lowpt2 ND START e \<sigma>'))) (head e)"
        using idk_traverse_edge
        by fast }
    thus ?thesis
      using idk_fold
      by blast
  qed
  thus ?case
    using "1.prems"(1)
    by (simp add: path_search_simps)
qed

lemma (in path_search) root_path_search:
  assumes "path_search_invar' N lowpt1 lowpt2 ND START v \<sigma>"
  shows "root (path_search N lowpt1 lowpt2 ND START v \<sigma>) = root \<sigma>"
  using assms
  thm path_search_induct
proof (induct rule: path_search_induct[OF assms, of _ N lowpt1 lowpt2 ND START v])
  case (1 N lowpt1 lowpt2 ND START v \<sigma>)
  hence "root (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>) = root \<sigma>"
  proof (induct "incidence_2 (multigraph \<sigma>) v" arbitrary: \<sigma>)
    case Nil
    thus ?case
      by simp
  next
    case (Cons e es)
    let ?\<sigma>' = "traverse_edge N lowpt1 lowpt2 ND START e \<sigma>"
    have
      "root (fold (traverse_edge N lowpt1 lowpt2 ND START) (incidence_2 (multigraph \<sigma>) v) \<sigma>) =
       root (fold (traverse_edge N lowpt1 lowpt2 ND START) es ?\<sigma>')"
      by (simp add: Cons.hyps(2)[symmetric])
    also have "... = root ?\<sigma>'"
    proof -
      have "es = incidence_2 (multigraph ?\<sigma>') v"
        thm Cons.prems(1)
        thm Cons.hyps(2)
        sorry
      moreover have "path_search_invar' N lowpt1 lowpt2 ND START v ?\<sigma>'"
        sorry
      ultimately show ?thesis
        using Cons.prems(1)
        thm Cons.hyps(1)
        by (auto simp add: Cons.hyps(2)[symmetric] intro: Cons.hyps(1))
    qed
    also have "... = root \<sigma>"
    proof (cases "tree_arc e \<sigma>")
      case True
      thm traverse_edge_def
      hence
        "root (traverse_edge N lowpt1 lowpt2 ND START e \<sigma>) =
         root (path_search N lowpt1 lowpt2 ND START (head e) (if START e then while_loop_1 \<sigma> else \<sigma>))"
        by (simp add: traverse_edge_def Let_def root_while_loop_3 root_while_loop_2 root_algorithm_6 root_algorithm_5)
      also have "... = root (if START e then while_loop_1 \<sigma> else \<sigma>)"
      proof -
        have "e \<in> set (incidence_2 (multigraph \<sigma>) v)"
          by (simp add: Cons.hyps(2)[symmetric])
        moreover have "path_search_invar' N lowpt1 lowpt2 ND START v (if START e then while_loop_1 \<sigma> else \<sigma>)"
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

lemma (in algorithm_3_pre_valid_input) set_ESTACK_eq_A:
  shows "set (ESTACK \<sigma>') = P.A (multigraph \<sigma>')"
  sorry
proof -
  thm tree_of_2.flatten.psimps
  have "set (ESTACK \<sigma>') = set (flatten (T_lookup (tree \<sigma>')) (incidence_2 (multigraph \<sigma>')) (root \<sigma>'))"
    unfolding path_search_invar_2 root_path_search
    by (simp add: init_def)
  also have "... = E (agublagu_2 (T_lookup (tree \<sigma>')) (incidence_2 (multigraph \<sigma>')) (root \<sigma>'))"
    by (simp add: a01)
  also have "... = E (incidence_2 (multigraph \<sigma>'))"
    using path_search_invar_\<sigma>'
    by
      (fastforce
        simp add: a02
        dest: path_search_invar.palm_tree palm_treeD(1))
  also have "... = P.A (multigraph \<sigma>')"
    by (simp add: edges_from_fun_incidence_eq_A)
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
      is_separation_pair: "is_separation_pair (undirect ` P.A (multigraph \<sigma>')) a b"
      by (auto simp add: set_ESTACK_eq_A)
    hence
      "a \<notin> Directed_Multigraph.V (edges_from_fun (\<lambda>v. incidence v (multigraph \<sigma>'))) \<or>
       b \<notin> Directed_Multigraph.V (edges_from_fun (\<lambda>v. incidence v (multigraph \<sigma>')))"
      using path_search_invar_\<sigma>' root_path_search
      sledgehammer
      thm path_search_invar_4
      using path_search_invar_4 by fastforce
      by
        (fastforce
          simp add: init_def idk_20
          dest: path_search_invar_4 path_search_invar.palm_tree)
    thus False
      using is_separation_pair
      by (auto simp add: edges_from_fun_incidence_eq_A V_image_undirect_eq dest: separation_pair_mem_V)
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