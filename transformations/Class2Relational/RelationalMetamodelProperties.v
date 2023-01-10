
Require Import List.

Require Import core.utils.Utils.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.
Require Import transformations.Class2Relational.ClassMetamodelProperties.

From transformations.Class2Relational Require Tactics.


(** *** Utilities on "getters" *)
(* not used *)
Remark getColumnsReferenceOnLinks_app :
        forall a b c,
         getColumnReferenceOnLinks c (a++b) = 
           match getColumnReferenceOnLinks c a with 
             Some r => Some r 
           | None => getColumnReferenceOnLinks c b end.
Proof.
  induction a ; simpl ; intros b c.
  + reflexivity.
  + destruct a.
  - auto.
  - destruct c0.
    destruct (beq_Column cr c).
    * reflexivity.
    * auto.
Qed.


Lemma in_get_2_right :
  forall (l: list Link) v (x:Table_t),
    In (ColumnReferenceLink {| cr := v ;  ct := x |}) l -> 
      exists r' : Table_t,
        getColumnReferenceOnLinks v l = return r'.
Proof.
  induction l ; simpl ; intros v x IN ; [ contradict IN | ].
  destruct_or IN.
  {
    subst a.
    rewrite lem_beq_Column_refl.
    eauto.
  }
  {
    apply (IHl v) in IN ; auto ; clear IHl ; [].
    destruct IN as [r G].
    rewrite G.
    destruct a ; eauto ; [].
    destruct c.
    destruct ( beq_Column cr v) ; eauto.
  }
Qed.

Corollary in_get_2_right_2 :
  forall (l: list Link) v, 
      (exists (x:Table_t), In (ColumnReferenceLink {| cr := v ;  ct := x |}) l) -> 
      exists r' : Table_t,
        getColumnReferenceOnLinks v l = return r'.
Proof.
  intros. 
  destruct H.
  eapply in_get_2_right.
  exact H.
Qed.

Lemma in_get_2_left :
  forall (l: list Link) col t, 
    getColumnReferenceOnLinks col l = return t -> 
    exists x,
    In (ColumnReferenceLink {| cr := col ;  ct := x |}) l  
      .
Proof.
  induction l ; simpl ; intros c r IN ; [ discriminate IN | ].

  destruct a.
  { (* table *)
    apply IHl in IN.
    destruct IN as [x IN] ; exists x ; right ; exact IN.
  }    
  { (* columns *)
    destruct c0.
    destruct(beq_Column cr c) eqn:E.
    {
      Tactics.inj IN.
      apply lem_beq_Column_id in E ; subst cr.
      eexists ; left ; reflexivity.
    }
    {
      apply IHl in IN.
      destruct IN as [x IN] ; exists x ; right ; exact IN.
    }
  }
Qed.


(** * well formedness  *)

Definition wf_target cm :=
  forall col r, 
    getColumnReference col cm =Some r ->
    In (TableElement r) cm.(modelElements).
