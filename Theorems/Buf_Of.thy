theory Buf_Of
imports AutoCorres
begin

install_C_file "../Files/buf_of.c"
autocorres [ heap_abs_syntax
] "../Files/buf_of.c"

context buf_of begin

thm write_char'_def
value write_char'

lemma write_char_overflow_check:
  "\<lbrace> \<lambda>s. is_valid_w8 s x
         \<and> sz = size_of TYPE(8 word)
         \<and> y = ptr_add x (of_nat sz)
         \<and> P (heap_w8 s y) \<rbrace>
     write_char' (ptr_coerce x) c
    \<lbrace> \<lambda> _ s. P (heap_w8 s y) \<rbrace>!"
oops
    
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