theory Buf_Of
imports AutoCorres
begin

install_C_file "../Files/buf_of.c"
autocorres [
    no_heap_abs = fill_buf,
    unsigned_word_abs = fill_buf
] "../Files/buf_of.c"

context buf_of begin

abbreviation "deref s x \<equiv> h_val (hrs_mem (t_hrs_' s)) x"

lemma buf_of_overflow_right:
  "\<lbrace> \<lambda>s. c_guard(x::8 word ptr)
         \<and> sz = size_of TYPE(8 word)
         \<and> nat i > 0 
         \<and> y = (ptr_add (ptr_add x (of_nat sz)) i)
         \<and> P (deref s y) \<rbrace>
     fill_buf' (ptr_coerce x) sz
    \<lbrace> \<lambda> _ s. P (deref s y) \<rbrace>"
    
    


end

end