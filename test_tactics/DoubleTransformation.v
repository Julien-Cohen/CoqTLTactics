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





(** Exemple de transformation avec deux out-pattern dans une règle. 

On va prendre un graphe et dupliquer las arcs, en mettant un arc dans le sens original et un arc dans le sens contraire pour chaque arc rencontré.

On voudrait une petite variation sur la transformation identité déjà implémentée, mais la syntaxe concrète ne prend pas en charge deux out-patterns dans les règles pour le moment.

Du coup je fais un copié-collé de la valeur de la transformation (issue du Print ci-dessous) que je modifie. 

 *)


Import ModelingMetamodel.


(*Require IdTransformation.
Print IdTransformation.T'.*)



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

