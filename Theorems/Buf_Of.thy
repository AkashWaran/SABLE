theory Buf_Of
imports AutoCorres
begin

install_C_file "../Files/buf_of.c"
autocorres [ 
] "../Files/buf_of.c"

context buf_of begin

thm write_char'_def
value write_char'

lemma noteq: "i \<noteq> 0 \<Longrightarrow> (x :: 8 word ptr) +\<^sub>p i \<noteq> x"
  apply (clarsimp simp: ptr_add_def)
  
sorry

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
    


end

end