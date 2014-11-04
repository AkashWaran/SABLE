theory Buf_Of
imports AutoCorres
begin

install_C_file "../Files/buf_of.c"
autocorres [
  heap_abs_syntax
] "../Files/buf_of.c"

context buf_of begin

declare [[ show_types ]]

theorem write_char_overflow_check:
  "\<lbrace> \<lambda>s. is_valid_w8 s x
         \<and> n = size_of TYPE(8 word)
         \<and> ptr_val y \<notin> {ptr_val x ..+ n}
         \<and> P (heap_w8 s y) \<rbrace>
     write_char' (ptr_coerce x) c
    \<lbrace> \<lambda> _ s. P (heap_w8 s y) \<rbrace>!"
  unfolding write_char'_def
  apply clarsimp
  apply wp
  apply (clarsimp simp:)
by (metis One_nat_def first_in_intvl fun_upd_apply zero_neq_one)
  
(* Old code below, ignore *)

(*
thm write_char'_def
value write_char'
  
lemma ptrEq: "Ptr (ptr_val x) = x"
  apply auto
  done  
  
lemma test2: "of_nat i - of_nat j = 0 \<Longrightarrow> of_nat i = of_nat j"
  
sorry
  
lemma test: "of_nat i = of_nat j \<Longrightarrow> i = j"
by (metis buf_of.test2 diff_0_eq_0 of_nat_0_eq_iff)
  
lemma natSubtraction: "of_nat i - of_nat j = 0 \<Longrightarrow> i = j"
by (metis buf_of.test buf_of.test2)
  
lemma natNumber: "(case Rep_Integ i of (i, j) \<Rightarrow> of_nat i - of_nat j) = 0 \<Longrightarrow> i = j"
  apply cases
  apply blast+
  apply clarsimp
by (smt2 Nat_Transfer.transfer_int_nat_relations(3) buf_of.test2 diff_is_0_eq semiring_1_class.of_nat_simps(2))
  
lemma of_int_i_impl: "of_int i = 0 \<Longrightarrow> i = 0"
  unfolding of_int_def
  apply clarsimp
  apply (erule natNumber)
  done

lemma ptrAdd: "i \<noteq> 0 \<Longrightarrow> ptr_val x + of_int i \<noteq> ptr_val x"
  apply auto;
  apply (drule of_int_i_impl)
  apply auto
  done
  
lemma ptrEqOnAdd: "i \<noteq> 0 \<Longrightarrow> Ptr (ptr_val x + of_int i) \<noteq> x"
  apply auto
  apply (drule ptrAdd ptrEq)
  apply auto
  by (metis buf_of.ptrAdd of_int_0 ptr_val.ptr_val_def)
  
lemma noteq: "i \<noteq> 0 \<Longrightarrow> (x :: 8 word ptr) +\<^sub>p i \<noteq> x"
  apply (clarsimp simp: ptr_add_def)
  apply (subgoal_tac "i > 0")
    apply (case_tac "i = 1")
      apply simp
      apply (metis add.commute add_right_cancel monoid_add_class.add.left_neutral ptr_val.ptr_val_def zero_neq_one)
    apply (subgoal_tac "i < 0")
    apply (case_tac "i = -1")   
      apply simp
      apply (metis linorder_not_le zless_add1_eq zless_imp_add1_zle)
    apply (drule ptrEqOnAdd)
    apply auto
    by (metis buf_of.ptrEqOnAdd)
      
lemma state: "i \<noteq> 0 \<Longrightarrow> ((heap_w8 s)(x := scast (of_int c))) (x +\<^sub>p i) = heap_w8 s (x +\<^sub>p i)"
  apply (simp only: fun_upd_apply)
  apply (drule noteq)
  apply (erule if_not_P)
done

theorem write_char_overflow_check:
  "\<lbrace> \<lambda>s. is_valid_w8 s x
         \<and> i \<noteq> 0
         \<and> y = ptr_add x i
         \<and> is_valid_w8 s y
         \<and> P (heap_w8 s y) \<rbrace>
     write_char' (ptr_coerce x) c
    \<lbrace> \<lambda> _ s. P (heap_w8 s y) \<rbrace>!"
  apply (unfold write_char'_def)
  apply clarsimp
  apply wp 
  apply clarsimp
  apply (subst state)
  apply auto
done
    
lemma buf_of_overflow_right:
  "\<lbrace> \<lambda>s. is_valid_w8 s x
         \<and> sz = size_of TYPE(8 word)
         \<and> nat i > 0 
         \<and> y = (ptr_add (ptr_add x (of_nat sz)) i)
         \<and> P (heap_w8 s y) \<rbrace>
     fill_buf' (ptr_coerce x) (of_nat sz) c
    \<lbrace> \<lambda> _ s. P (heap_w8 s y) \<rbrace>!"
    sorry
*)    


end

end