(** Some tactics to unfold accessors *)
From core Require Import Syntax.


#[global]
Hint Unfold 
   r_name r_guard r_iterator r_outputPattern 
  : rule_accessors.

#[global]
Hint Unfold 
   opu_name opu_element opu_link 
  : opu_accessors.


