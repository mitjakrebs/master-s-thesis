theory Partitions_Ext
  imports
    Vickrey_Clarke_Groves.Partitions
begin

(*
definition is_partition_generalization :: "'a set set \<Rightarrow> bool" where
  "is_partition_generalization \<C> \<equiv> \<forall>C1\<in>\<C>. \<forall>C2\<in>\<C>. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}"

definition is_partition_generalization_of :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_partition_generalization_of A \<C> \<equiv> is_partition_generalization \<C> \<and> \<Union> \<C> = A"

definition is_partition :: "'a set set \<Rightarrow> bool" where
  "is_partition \<C> \<equiv> is_partition_generalization \<C> \<and> {} \<notin> \<C>"

definition is_partition_of :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_partition_of A \<C> \<equiv> is_partition \<C> \<and> \<Union> \<C> = A"

lemma
  shows "is_partition_of A \<C> \<longleftrightarrow> is_partition_generalization_of A \<C> \<and> {} \<notin> \<C>"
  by (auto simp add: is_partition_of_def is_partition_def is_partition_generalization_of_def)
*)

end