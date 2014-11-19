theory Buf_Of
imports AutoCorres
begin

install_C_file "../Files/buf_of.c"
autocorres [
  heap_abs_syntax,
  no_heap_abs = write_char_unsafe write_chars_unsafe
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

thm outside_intvl_range

(* NOTE : We do not consider cases where the buffer wraps around as this goes into the else clause *)
lemma outside_intvl_range' :
"p \<notin> {a..+b} \<and> a \<noteq> 0 \<Longrightarrow> if a + of_nat b = 0 then p < a \<and> a + of_nat b \<le> p else p < a \<or> a + of_nat b \<le> p"
  apply (case_tac "a + of_nat b \<noteq> 0")
    apply (metis outside_intvl_range)
  apply clarsimp
  apply unat_arith
  apply clarsimp
by (smt2 Abs_fnat_hom_add Nat.add_diff_inverse add_less_cancel_left intvlI unat_less_helper unat_lt2p word_of_nat_less word_unat.Rep_inverse)

theorem write_chars_overflow_check:
  "\<lbrace>\<lambda>s. buf = {ptr_val (x::8 word ptr) ..+ (unat n * size_of TYPE(8 word))}
         \<and> ptr_val y \<notin> buf
         \<and> 0 \<notin> buf
         \<and> P (heap_w8 s y) 
         \<and> (\<forall>z u. ptr_val z \<in> buf \<longrightarrow> is_valid_w8 u z) \<rbrace>
     write_chars' (ptr_coerce x) c n
    \<lbrace> \<lambda> _ s. P (heap_w8 s y) \<rbrace>!"
  unfolding write_chars'_def
  apply (rule validNF_assume_pre)
  apply clarsimp
  apply wp
  apply (subst whileLoop_add_inv [where M="\<lambda>(n', _). n - n'"
                and I="\<lambda>n' s. n' \<le> n \<and> P (heap_w8 s y)"])
  apply wp
  apply safe
  apply unat_arith
  prefer 2
  apply unat_arith
  prefer 3
  apply auto
  apply (frule outside_intvl_range)
  apply (erule disjE)
  apply (subst fun_upd_apply)
  apply (simp add: ptr_add_def, rule impI)
  apply (erule_tac Q = "ptr_val y < ptr_val x" in contrapos_pp)
  apply (rule leD)
  apply (drule zero_not_in_intvl_no_overflow)
  apply unat_arith
  apply (subst fun_upd_apply)
  apply (simp add: ptr_add_def, rule impI)
  apply (drule_tac y = "ptr_val x + n" in leD)
  apply (erule_tac Q = "ptr_val y < ptr_val x + n" in contrapos_np)
  apply (drule zero_not_in_intvl_no_overflow)
  apply clarsimp
  apply unat_arith
  apply clarsimp
  apply (metis intvlI word_unat.Rep_inverse)
  apply (erule_tac x="x +\<^sub>p uint n'" in allE)
  apply (erule impE)
  apply (simp add:ptr_add_def)
  apply (metis intvlI word_less_nat_alt word_unat.Rep_inverse) 
  sorry

abbreviation "deref s x \<equiv> h_val (hrs_mem (t_hrs_' s)) x"

theorem write_char_overflow_check_type_unsafe:
  "\<lbrace> \<lambda>s. c_guard (x :: 8 word ptr)
         \<and> n = size_of TYPE(8 word)
         \<and> ptr_val (y :: 8 word ptr) \<notin> {ptr_val x ..+ n}
         \<and> P (deref s y) \<rbrace>
     write_char_unsafe' (ptr_coerce x) c
    \<lbrace> \<lambda> _ s. P (deref s y) \<rbrace>!"
  unfolding write_char_unsafe'_def
  apply (clarsimp simp: skip_def)
  apply wp
  apply (clarsimp simp: hrs_mem_update heap_update_def h_val_def)
  apply (subst heap_update_nmem_same)
  apply (metis length_Cons list.size(3) to_bytes_word8)
  apply assumption
done
  
theorem write_chars_overflow_check_type_unsafe:
  "\<lbrace> \<lambda>s. buf = {ptr_val x ..+ (unat n * size_of TYPE(8 word))}
         \<and> 0 \<notin> buf
         \<and> ptr_val (y :: 8 word ptr) \<notin> buf
         \<and> unat n < addr_card
         \<and> P (deref s y) \<rbrace>
     write_chars_unsafe' (ptr_coerce x) c n
    \<lbrace> \<lambda> _ s. P (deref s y) \<rbrace>!"
  unfolding write_chars_unsafe'_def
  apply (rule validNF_assume_pre)
  apply clarsimp
  apply wp
  apply (subst whileLoop_add_inv [where M="\<lambda>(n', _). n - n'"
                and I="\<lambda>n' s. n' \<le> n \<and> P (deref s y)"])
  apply wp
  apply safe
  apply unat_arith
  apply (clarsimp simp: hrs_mem_update h_val_def heap_update_def)
  apply (subst heap_update_nmem_same)
  apply simp_all
  apply (simp add: ptr_add_def)
  apply (erule_tac P = "ptr_val y \<notin> {ptr_val x..+unat n}" in rev_notE)
  apply simp
  apply (drule intvl_Suc)
  apply (drule_tac t = "ptr_val y" in sym)
  apply simp
  apply (simp add: intvl_def)
  apply (rule_tac x = "unat n'" in exI)
  apply unat_arith
  apply unat_arith
  apply (simp add: c_guard_def)
  apply (simp add: c_null_guard_def)
  apply (simp add: ptr_aligned_def)
  apply (simp add: ptr_add_def)
  apply unat_arith
  apply auto
  apply (metis intvlI intvl_Suc word_unat.Rep_inverse)
done

thm test_func'_def

theorem test_func_ok:
  "\<lbrace> \<lambda>s. True \<rbrace>
     test_func'
    \<lbrace> \<lambda> _ s. True \<rbrace>!"
  
sorry

end

end
