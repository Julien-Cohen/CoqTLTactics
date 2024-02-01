(** Graph Identity transformation. *)

Require Import String List.


From core 
  Require Import utils.Utils TransformationConfiguration.

From core.modeling 
  Require Import 
  (*ConcreteSyntax*) ModelingSemantics ConcreteExpressions Parser ModelingTransformationConfiguration.

From test_tactics
  Require 
  BasicMetamodel .

Import Glue.


#[export]
Instance IdTransformationConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration BasicMetamodel.MM BasicMetamodel.MM.

#[export]  
Instance Moore2MealyModelingTransformationConfiguration : ModelingTransformationConfiguration IdTransformationConfiguration :=
 Build_ModelingTransformationConfiguration IdTransformationConfiguration BasicMetamodel.MMM BasicMetamodel.MMM.

Open Scope coqtl.


Import BasicMetamodel. 


(** Exemple de transformation avec deux out-pattern dans une règle. 

On va prendre un graphe et dupliquer las arcs, en mettant un arc dans le sens original et un arc dans le sens contraire pour chaque arc rencontré.

On voudrait une petite variation sur la transformation identité déjà implémentée, mais la syntaxe concrète ne prend pas en charge deux out-patterns dans les règles pour le moment.

Du coup je fais un copié-collé de la valeur de la transformation (issue du Print ci-dessous. 

Toutefois, l'inférence de type échoue, alors je pose des définitions intermédiaires pour aider celle-ci (f1, f2, f3, f4 ci-dessous, puis f2', f3' et f4' pour la génération d'arcs inversés). *)


Require IdTransformation.
Print IdTransformation.T'.

Definition f1 : denoteSignature [Node_K]
    (option (ModelingMetamodel.denoteEDatatype Node_K)) := fun
                (s : ModelingMetamodel.denoteEDatatype Node_K) =>
              return s.

Definition f2 : denoteSignature [Arrow_K]
                  (option (ModelingMetamodel.denoteEDatatype Arrow_K)) :=
  fun (t : ModelingMetamodel.denoteEDatatype Arrow_K) =>
    return t.

                    Definition f3 : list PoorTraceLink.TraceLink ->nat ->  SourceModel -> denoteSignature [Arrow_K]
    (ModelingMetamodel.denoteEDatatype Arrow_K ->
     option (ModelingMetamodel.denoteLDatatype Arrow_source_K)) := 
fun (tls : list PoorTraceLink.TraceLink) 
                    (_ : nat) (m : SourceModel) => 
                      fun
                    (moore_tr
                     mealy_tr : ModelingMetamodel.denoteEDatatype
                                  Arrow_K) =>
                  t_source <- Arrow_getSourceObject moore_tr m;
                  res <- resolve tls "s" Node_K (singleton t_source);
                  do_glue mealy_tr with res.



                 Definition f4 : list PoorTraceLink.TraceLink -> nat -> SourceModel -> denoteSignature [Arrow_K]
    (ModelingMetamodel.denoteEDatatype Arrow_K ->
     option (ModelingMetamodel.denoteLDatatype Arrow_target_K)) := fun (tls : list PoorTraceLink.TraceLink) 
                   (_ : nat) (m : SourceModel)
                   (moore_tr
                    mealy_tr : ModelingMetamodel.denoteEDatatype
                                 Arrow_K) =>
                 t_target <- Arrow_getTargetObject moore_tr m;
                 res <- resolve tls "s" Node_K (singleton t_target);
                 do_glue mealy_tr with res.

Definition f2' : denoteSignature [Arrow_K]
                  (option (ModelingMetamodel.denoteEDatatype Arrow_K)) :=
  fun (t : ModelingMetamodel.denoteEDatatype Arrow_K) =>
    return {| Arrow_id := t.(Arrow_id) +1 |} .

(* renvoie une source de transition, mais on veut la cible de l'ancienne transition pour renverser le sens de la flèche *)
 Definition f3' : list PoorTraceLink.TraceLink ->nat ->  SourceModel -> denoteSignature [Arrow_K]
    (ModelingMetamodel.denoteEDatatype Arrow_K ->
     option (ModelingMetamodel.denoteLDatatype Arrow_source_K)) := 
fun (tls : list PoorTraceLink.TraceLink) 
                    (_ : nat) (m : SourceModel) => 
                      fun
                    (moore_tr
                     mealy_tr : ModelingMetamodel.denoteEDatatype
                                  Arrow_K) =>
                  t_source <- Arrow_getTargetObject moore_tr m;
                  res <- resolve tls "s" Node_K (singleton t_source);
                  do_glue mealy_tr with res.


(* renvoie une cible de transition, mais on veut la source de l'ancienne transition pour renverser le sens de la flèche. *)
                 Definition f4' : list PoorTraceLink.TraceLink -> nat -> SourceModel -> denoteSignature [Arrow_K]
    (ModelingMetamodel.denoteEDatatype Arrow_K ->
     option (ModelingMetamodel.denoteLDatatype Arrow_target_K)) := fun (tls : list PoorTraceLink.TraceLink) 
                   (_ : nat) (m : SourceModel)
                   (moore_tr
                    mealy_tr : ModelingMetamodel.denoteEDatatype
                                 Arrow_K) =>
                 t_target <- Arrow_getSourceObject moore_tr m;
                 res <- resolve tls "s" Node_K (singleton t_target);
                 do_glue mealy_tr with res.

Definition T' : ConcreteSyntax.ConcreteTransformation := {|
  ConcreteSyntax.concreteRules :=
    [{|
       ConcreteSyntax.r_name := "state";
       ConcreteSyntax.r_InKinds := [Node_K];
       ConcreteSyntax.r_guard := None;
       ConcreteSyntax.r_iter := None;
       ConcreteSyntax.r_outpat :=
         [{|
            ConcreteSyntax.e_OutKind := Node_K;
            ConcreteSyntax.e_name := "s";
            ConcreteSyntax.e_outpat :=  
              fun (_ : nat) (_ : SourceModel) => f1 ;
            ConcreteSyntax.e_outlink := nil
          |}]
     |}
;
    {|
      ConcreteSyntax.r_name := "transition";
      ConcreteSyntax.r_InKinds := [Arrow_K];
      ConcreteSyntax.r_guard :=
        return (fun (_ : SourceModel)
                  (_ : ModelingMetamodel.denoteEDatatype Arrow_K) =>
                true);
      ConcreteSyntax.r_iter := None;
      ConcreteSyntax.r_outpat :=
        [{|
           ConcreteSyntax.e_OutKind := Arrow_K;
           ConcreteSyntax.e_name := "t";
           ConcreteSyntax.e_outpat :=
             fun (_ : nat) (_ : SourceModel) => f2
               ;
           ConcreteSyntax.e_outlink :=
             [{|
                ConcreteSyntax.o_OutRefKind := Arrow_source_K;
                ConcreteSyntax.o_outpat :=
               f3  
               
              |};
             {|
               ConcreteSyntax.o_OutRefKind := Arrow_target_K;
               ConcreteSyntax.o_outpat := f4    

             |}]
         |} ;
         (* second output pattern in the rule *)
{|
           ConcreteSyntax.e_OutKind := Arrow_K;
           ConcreteSyntax.e_name := "t";
           ConcreteSyntax.e_outpat :=
             fun (_ : nat) (_ : SourceModel) => f2'
               ;
           ConcreteSyntax.e_outlink :=
             [{|
                ConcreteSyntax.o_OutRefKind := Arrow_source_K;
                ConcreteSyntax.o_outpat :=
               f3'
               
              |};
             {|
               ConcreteSyntax.o_OutRefKind := Arrow_target_K;
               ConcreteSyntax.o_outpat := f4'    

             |}]
         |}]
    |} ]
|}.

Definition T := parse T'.

Close Scope coqtl.

