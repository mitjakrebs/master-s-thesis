(* TODO: Rename. *)
theory Idk
  imports
    Walk
begin

context other
begin

definition tbd :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) edge \<Rightarrow> ('a, 'b) multigraph" where
  "tbd G X e \<equiv>
   {e'. \<exists>p u v. walk G p u v \<and>
                e \<in> set p \<and>
                e' \<in> set p \<and>
                set (tl (butlast (walk_vertices p u))) \<inter> X = {}}"

lemma tbd_subset:
  shows "tbd G X e \<subseteq> G"
  sorry

definition tbds :: "('a, 'b) multigraph \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) multigraph set" where
  "tbds G X \<equiv> {E. \<exists>e\<in>G. E = tbd G X e}"

lemma tbds_image_cong:
  shows "tbds G X = (tbd G X) ` G"
  by (auto simp add: tbds_def)

end

end