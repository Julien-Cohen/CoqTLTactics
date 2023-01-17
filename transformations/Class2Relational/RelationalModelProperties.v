
Require Import List.

Require Import core.utils.Utils.
Require Import core.Model.

From transformations.Class2Relational
  Require Import Class2Relational ClassMetamodel RelationalMetamodel.


From transformations.Class2Relational Require Tactics.


(** *** Utilities on "getters" *)

(* Not Used *)
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

(* Used *)
Lemma in_getColumnReferenceOnLinks_right :
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

(* Used *)
Corollary in_getColumnReferenceOnLinks_right_2 :
  forall (l: list Link) v, 
      (exists (x:Table_t), In (ColumnReferenceLink {| cr := v ;  ct := x |}) l) -> 
      exists r' : Table_t,
        getColumnReferenceOnLinks v l = return r'.
Proof.
  intros. 
  destruct H.
  eapply in_getColumnReferenceOnLinks_right.
  exact H.
Qed.

(* Used *)
Lemma in_getColumnReferenceOnLinks_left :
  forall (l: list Link) col t, 
    getColumnReferenceOnLinks col l = return t -> 
    In (ColumnReferenceLink {| cr := col ;  ct := t |}) l  
      .
Proof.
  induction l ; simpl ; intros c r IN ; [ discriminate IN | ].

  destruct a.
  { (* table *)
    apply IHl in IN.
    right ; exact IN.
  }    
  { (* columns *)
    destruct c0.
    destruct(beq_Column cr c) eqn:E.
    {
      Tactics.inj IN.
      apply lem_beq_Column_id in E ; subst cr.
      left ; reflexivity.
    }
    {
      apply IHl in IN.
      right ; exact IN.
    }
  }
Qed.


(** * Well Formedness  *)

(* Used *)
Definition wf_all_table_references_exist (rm:RelationalModel) :=
  forall col r, 
    In (ColumnReferenceLink {| cr := col ;  ct := r |}) rm.(modelLinks) ->
    In (TableElement r) rm.(modelElements).

