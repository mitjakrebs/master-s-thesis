theory Incidence_Structure
  imports
    "../../Orderings_Ext"
    "HOL-Data_Structures.Set_Specs"
begin

locale Incidence_Structure =
  fixes empty :: 'g
  fixes insert :: "'b::linorder \<Rightarrow> 'a::linorder \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
  fixes delete :: "'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'g \<Rightarrow> 'g"
  fixes incidence :: "'b \<Rightarrow> 'g \<Rightarrow> ('a \<times> 'b) list"
  fixes invar :: "'g \<Rightarrow> bool"
  assumes incidence_empty: "incidence v empty = []"
  assumes incidence_insert:
    "invar G \<and> Sorted_Less.sorted (incidence v G) \<Longrightarrow>
     incidence v (insert x p G) = (if v = x then ins_list p (incidence v G) else incidence v G)"
  assumes incidence_delete:
    "invar G \<and> Sorted_Less.sorted (incidence v G) \<Longrightarrow>
     incidence v (delete x p G) = (if v = x then List_Ins_Del.del_list p (incidence v G) else incidence v G)"
  assumes invar_empty: "invar empty"
  assumes invar_insert: "invar G \<and> Sorted_Less.sorted (incidence v G) \<Longrightarrow> invar (insert v p G)"
  assumes invar_delete: "invar G \<and> Sorted_Less.sorted (incidence v G) \<Longrightarrow> invar (delete v p G)"

definition (in Incidence_Structure) invar' :: "'g \<Rightarrow> bool" where
  "invar' G \<equiv> invar G \<and> (\<forall>v. Sorted_Less.sorted (incidence v G))"

lemma (in Incidence_Structure) invar'_empty:
  shows "invar' empty"
  using invar_empty
  by (simp add: invar'_def incidence_empty)

lemma (in Incidence_Structure) invar'_insert:
  assumes "invar' G"
  shows "invar' (insert v p G)"
  using assms
  by (auto simp add: invar'_def incidence_insert intro: invar_insert sorted_ins_list)

lemma (in Incidence_Structure) invar'_delete:
  assumes "invar' G"
  shows "invar' (delete v p G)"
  using assms
  by (auto simp add: invar'_def incidence_delete intro: invar_delete sorted_del_list)

end