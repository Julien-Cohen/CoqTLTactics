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



Lemma in_allTuples_singleton :
  forall e t s, 
    In [e] (allTuples t s) ->
    In e s.(modelElements).
Proof.
  intros e t s IN.
  apply incl_singleton.
  eapply Certification.allTuples_incl.
  exact IN.
Qed.





Theorem All_classes_instantiate_impl:
  Monotonicity Class2Relational.
Proof.
  unfold Monotonicity.
  unfold TargetModel_elem_incl. unfold SourceModel_elem_incl.
  unfold incl.
  intros sm1 sm2 INC a IN.

  Tactics.destruct_execute.

  apply in_flat_map.
  
  Tactics.show_singleton.    
  apply in_allTuples_singleton in IN_E.

  apply INC in IN_E ; clear INC.
  exists ([e]).
  split.
  { 
    apply allTuples_incl_length ; [ | simpl ; solve[auto] ].
    apply incl_singleton.
    assumption.
  }
  { 
    repeat Tactics.destruct_any.
    clear IN_I.

    (* Two ways of reasonning by case analysis : (1) decompose e, (2) decompose r *)
    (* Here we first decompose r and then we deduce e. *)

    destruct_In_two ;
      simpl in IN_OP; 
      unfold In in IN_OP ;
      remove_or_false IN_OP ;
      subst ope  ;  
      simpl in M ;
      deduce_element_kind_from_guard ;
      compute in IN ; Tactics.inj IN .
    
    { (* first rule *)      
      compute ; auto.
    }
    { (* second rule *)
      (* To compute we need to know the value of a.(derived) *) 
      destruct a0 ; simpl in * ; subst. 
      compute ; auto.
    }
  }
Qed.

Theorem All_classes_instantiate_impl_alt:
  Monotonicity Class2Relational.
Proof.
  unfold Monotonicity.
  unfold TargetModel_elem_incl. unfold SourceModel_elem_incl.
  unfold incl.
  intros sm1 sm2 INC a IN.
  
  Tactics.destruct_execute.
  
  apply in_flat_map.
  
  Tactics.show_singleton.    
  apply in_allTuples_singleton in IN_E.
  
  apply INC in IN_E ; clear INC.
  exists ([e]).
  split.
  { 
    apply allTuples_incl_length ; [ | simpl ; solve[auto] ].
    apply incl_singleton.
    assumption.
  }
  { 
    repeat Tactics.destruct_any.
    clear IN_I.
    
    (* Two ways of reasonning by case analysis : (1) decompose e, (2) decompose r *)
    (* Here we first decompose e, and then we decompose r. *)

    
    destruct e.
    
    { (* ClassElement *)
      Tactics.destruct_In_two ;
       simpl in IN_OP ;
       remove_or_false IN_OP ;
       subst ope ; 
       compute in IN ; (* optional *)
       [ Tactics.inj IN | discriminate IN (*the second rule cannot match *)].
       simpl ; auto.
    }

    {
      (* AttributeElement *)
      (* To compute we need to know the value of a.(derived) *) 
      Tactics.destruct_In_two ;
       simpl in IN_OP ;
       remove_or_false IN_OP ;
       subst ope  ;
       simpl in M ;
       try deduce_element_kind_from_guard ;
       compute in IN (* optional *); 
      [ discriminate IN (* the first rule cannot match *) | Tactics.inj IN ].

      destruct a1 ; simpl in D ; subst derived.
      simpl ; auto.
    }
  }
Qed.
 
(** Generalisation ? If the guard depends only on the input element and not on the other elements of the input model, then the transformation s monotonic ? *)
