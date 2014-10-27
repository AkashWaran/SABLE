theory Sample
imports AutoCorres
begin

install_C_file "../Files/sample.c"
autocorres [
    no_heap_abs = writeBuffer,
    unsigned_word_abs = writeBuffer
] "../Files/sample.c"

context sample begin

abbreviation "deref s x \<equiv> h_val (hrs_mem (t_hrs_' s)) x"

lemma writeBuffer_overflow_right:
  "\<lbrace> \<lambda>s. c_guard(x::8 word ptr)
         \<and> sz = size_of TYPE(8 word)
         \<and> nat i > 0 
         \<and> y = (ptr_add (ptr_add x (of_nat sz)) i)
         \<and> P (deref s y) \<rbrace>
     writeBuffer' x sz
    \<lbrace> \<lambda> _ s. P (deref s y) \<rbrace>"
    
    


end

end