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

Import BasicMetamodel. 

#[export]
Instance Id_TC : 
  TransformationConfiguration := 
  Build_TransformationConfiguration MM MM.



#[export]  
Instance Id_MTC : 
  ModelingTransformationConfiguration Id_TC :=
  Build_ModelingTransformationConfiguration Id_TC MMM MMM.

Open Scope coqtl.


(** 
    Example of transformation with two out-patterns in the same rule. 

    The transformation takes a graph and duplicates the edges, except that a duplicated edge is the opposite as the inital one. 
        
     Ideally, it would be a small variation on the identity tansformation, but double output-patterns are not supported by the notation shortcuts for concrete syntax of CoqTL, so we use the Coq data-type instead.
 
 *)


Import ModelingMetamodel.

Definition T' := 
  {|
    concreteRules :=
      [{| (* first rule *)
          r_name := "state";
          r_InKinds := [Node_K];
          r_guard := None;
          r_iter := None;
          r_outpat :=
            [{|
                e_OutKind := Node_K;
                e_name := "s";
                e_outpat :=
                  fun (_ : nat) (_ : SourceModel) => (fun
                                                         (s : Node_t) => return s) :
                    denoteSignature [Node_K] (option (denoteEDatatype Node_K));
                e_outlink := nil
              |}]
        |};

       {| (* second rule *)
         r_name := "transition";
         r_InKinds := [Arrow_K];
         r_guard := None ;
         r_iter := None ;
         r_outpat :=
           [
             
          (* first output pattern *)
             {|
               e_OutKind := Arrow_K;
               e_name := "t";
               e_outpat :=
                 fun (_ : nat) (_ : SourceModel) =>
                   ((fun (t : denoteEDatatype Arrow_K) => return t) 
                     : denoteSignature [Arrow_K] (option (denoteEDatatype Arrow_K)));
               e_outlink :=
                 [{|
                     o_OutRefKind := Arrow_source_K;
                     o_outpat :=
                       fun (tls : list PoorTraceLink.TraceLink) 
                           (_ : nat) (m : SourceModel) =>
                         
                         ((fun (a b : denoteEDatatype Arrow_K) =>
                             t_source <- Arrow_getSourceObject a m;
                           res <- resolve tls "s" Node_K (singleton t_source);
                           do_glue b with res) 
                           : denoteSignature [Arrow_K]
                               (denoteEDatatype Arrow_K ->
                                option (denoteLDatatype Arrow_source_K)))
                   |};
                  {|
                    o_OutRefKind := Arrow_target_K;
                    o_outpat :=
                      fun (tls : list PoorTraceLink.TraceLink) 
                          (_ : nat) (m : SourceModel) => 
                        
                        ( (fun (a b : denoteEDatatype Arrow_K) =>
                             t_target <- Arrow_getTargetObject a m;
                           res <- resolve tls "s" Node_K (singleton t_target);
                           do_glue b with res) 
                          : denoteSignature [Arrow_K]
                              (denoteEDatatype Arrow_K ->
                               option (denoteLDatatype Arrow_target_K)))
                  |}]
             |}
               
             ;
             
             (* second output pattern *)
             {|
               e_OutKind := Arrow_K;
               e_name := "back_t";
               e_outpat :=
                 fun (_ : nat) (_ : SourceModel) =>
                   ((fun t => return {| Arrow_id := t.(Arrow_id) +1 |}) (* increment the id *)
                     : denoteSignature [Arrow_K] (option (denoteEDatatype Arrow_K)));
               e_outlink :=
                 [{|
                     o_OutRefKind := Arrow_source_K;
                     o_outpat :=
                       fun (tls : list PoorTraceLink.TraceLink) 
                           (_ : nat) (m : SourceModel) =>
                         
                         ((fun (a b : denoteEDatatype Arrow_K) =>
                             t_source <- Arrow_getTargetObject (* instead of source *) a m;
                           res <- resolve tls "s" Node_K (singleton t_source);
                           do_glue b with res) 
                           : denoteSignature 
                               [Arrow_K]
                               (denoteEDatatype Arrow_K -> option (denoteLDatatype Arrow_source_K)))
                   |};
                  {|
                    o_OutRefKind := Arrow_target_K;
                    o_outpat :=
                      fun (tls : list PoorTraceLink.TraceLink) 
                          (_ : nat) (m : SourceModel) => 
                        
                        ( (fun (a b : denoteEDatatype Arrow_K) =>
                             t_target <- Arrow_getSourceObject (* instead of target *) a m;
                           res <- resolve tls "s" Node_K (singleton t_target);
                           do_glue b with res) 
                          : denoteSignature [Arrow_K]
                              (denoteEDatatype Arrow_K -> option (denoteLDatatype Arrow_target_K)))
                  |}]
             |}
           ]
       |}]
  |}
.

Definition T := parse T'.

Close Scope coqtl.

