(** Graph Identity transformation. *)

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
Instance Id_TransformationConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration BasicMetamodel.MM BasicMetamodel.MM.

#[export]  
Instance Id_ModelingTransformationConfiguration : ModelingTransformationConfiguration Id_TransformationConfiguration :=
 Build_ModelingTransformationConfiguration Id_TransformationConfiguration BasicMetamodel.MMM BasicMetamodel.MMM.

Open Scope coqtl.


Import BasicMetamodel. 



Definition T' :=
    transformation
    [
      rule "state"
      from [Node_K]
      to [
        ELEM "s" ::: Node_K  
           fun _ _ s => return s 
      ];

      rule "transition"
      from [Arrow_K]
      where (fun m a => true)

      to [
        ELEM "t" ::: Arrow_K
           fun _ m t => return t  
          
        LINK ::: Arrow_source_K 
           fun tls _ m a b =>
             t_source <- Arrow_getSourceObject a m ;
             res <- resolve tls "s" Node_K (singleton t_source) ;
             do_glue b with res 
           ;

        LINK ::: Arrow_target_K 
           fun tls _ m a b =>
             t_target <- Arrow_getTargetObject a m ;
             res <- resolve tls "s" Node_K (singleton t_target) ;
             do_glue b with res 
          
      ]
].

Definition T := parse T'.

Close Scope coqtl.

