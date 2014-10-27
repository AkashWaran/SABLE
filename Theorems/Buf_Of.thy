theory Buf_Of
imports AutoCorres
begin

install_C_file "../Files/buf_of.c"
autocorres [
    no_heap_abs = fill_buf write_char,
    unsigned_word_abs = fill_buf write_char
] "../Files/buf_of.c"

context buf_of begin

abbreviation "deref s x \<equiv> h_val (hrs_mem (t_hrs_' s)) x"

lemma write_char_overflow_check:
  "\<lbrace> \<lambda>s. c_guard(x::8 word ptr)
         \<and> sz = size_of TYPE(8 word)
         \<and> nat i > 0 
         \<and> y = (ptr_add (ptr_add x (of_nat sz)) i)
         \<and> P (deref s y) \<rbrace>
     write_char' (ptr_coerce x) c
    \<lbrace> \<lambda> _ s. P (deref s y) \<rbrace>"
    oops
    

lemma buf_of_overflow_right:
  "\<lbrace> \<lambda>s. c_guard(x::8 word ptr)
         \<and> sz = size_of TYPE(8 word)
         \<and> nat i > 0 
         \<and> y = (ptr_add (ptr_add x (of_nat sz)) i)
         \<and> P (deref s y) \<rbrace>
     fill_buf' (ptr_coerce x) sz c
    \<lbrace> \<lambda> _ s. P (deref s y) \<rbrace>"
    sorry
    


end

end