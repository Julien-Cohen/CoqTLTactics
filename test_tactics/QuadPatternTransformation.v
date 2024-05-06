

Require Import String List.


From core 
  Require Import utils.Utils TransformationConfiguration.

From core.modeling 
  Require Import 
  ConcreteSyntax ModelingSemantics ConcreteExpressions Parser ModelingTransformationConfiguration.

From test_tactics
  Require 
  BasicMetamodel .

Import Glue.


#[export]
Instance Combi_TransformationConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration BasicMetamodel.MM BasicMetamodel.MM.

#[export]  
Instance Combi_ModelingTransformationConfiguration : ModelingTransformationConfiguration Combi_TransformationConfiguration :=
 Build_ModelingTransformationConfiguration Combi_TransformationConfiguration BasicMetamodel.MMM BasicMetamodel.MMM.

Open Scope coqtl.


Import BasicMetamodel. 

(* This is a transformation with a pattern of size 4. *)
Definition T' :=
    transformation
    [
      rule "state"
      from [Node_K ; Node_K ; Node_K ; Node_K]
      to [
        ELEM "s" ::: Node_K  
           fun _ _ _ _ _ _ =>  return {| Node_id := 1 |} 
      ]].

Definition Quad_T := parse T'.

Close Scope coqtl.

