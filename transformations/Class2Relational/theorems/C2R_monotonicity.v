Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.properties.monotonicity.Monotonicity.

From transformations.Class2Relational
  Require Import 
  Class2Relational
  ClassMetamodel
  RelationalMetamodel
  Tactics.

Require Import core.utils.CpdtTactics.

Theorem All_classes_instantiate_impl:
  Monotonicity Class2Relational.
Proof.
  unfold Monotonicity.
  unfold TargetModel_elem_incl. unfold SourceModel_elem_incl.
  unfold incl.
  simpl.
  intros.

  apply in_flat_map.
  apply in_flat_map in H0. repeat destruct H0.
  exists x.
  Tactics.show_singleton.    
  split.
  { 
    apply allTuples_incl_length ; [ | simpl ; solve[auto] ].
    apply incl_singleton.
    apply H ; clear H.
    
    apply Certification.allTuples_incl in H0.
    apply incl_singleton in H0.
    assumption.
  }
  { 
    repeat destruct_any.
    clear IN_I.
    Tactics.destruct_In_two ;
    simpl in * ;
    remove_or_false IN_OP ;
    subst ope ; simpl in *.
    
    { (* first rule *)
      unfold ConcreteExpressions.makeElement in H1 ; simpl in H1.
      unfold ConcreteExpressions.wrapElement  in H1 ; simpl in H1.
      unfold TransformationConfiguration.SourceElementType in e.
      compute in e.
      simpl in e.
      
      destruct e ; [ | exfalso] ; simpl in *.
      * injection H1 ; clear H1 ; subst.
        auto.
      * discriminate.
    }
    { (* second rule *)
      unfold ConcreteExpressions.makeElement in H1 ; simpl in H1.
      unfold ConcreteExpressions.wrapElement  in H1.
      
      destruct e ; [ exfalso | ] ;simpl in *.
      * discriminate H1.
      * injection H1 ; clear H1 ; intros ; subst ; simpl in *.
        
        unfold ConcreteExpressions.makeGuard in M.
        unfold ConcreteExpressions.wrap in M.
        simpl in M.
        apply Bool.negb_true_iff in M.
        
        destruct a0 ; simpl in *.
        subst derived.
        
        simpl ; auto.
    }
  }
Qed.
           
