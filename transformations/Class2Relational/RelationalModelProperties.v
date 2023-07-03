
Require Import List.

Require Import core.utils.Utils.
Require Import core.Model.

From transformations.Class2Relational
  Require Import Class2Relational ClassMetamodel RelationalMetamodel.


From transformations.Class2Relational 
  Require C2RTactics.


(** *** Utilities on "getters" *)

(* Not Used *)
Remark getColumnsReferenceOnLinks_app :
        forall a b c,
         getColumn_referenceOnLinks c (a++b) = 
           match getColumn_referenceOnLinks c a with 
             Some r => Some r 
           | None => getColumn_referenceOnLinks c b end.
Proof.
  induction a ; simpl ; intros b c.
  + reflexivity.
  + destruct a.
  - auto.
  - destruct c0.
    destruct (Column_t_beq Column_reference_t_lglue c).
    * reflexivity.
    * auto.
Qed.

(* Used *)
Lemma in_getColumnReferenceOnLinks_right :
  forall (l: list Link) v (x:Table_t),
    In (Column_referenceLink {| Column_reference_t_lglue := v ;  Column_reference_t_rglue := x |}) l -> 
      exists r' : Table_t,
        getColumn_referenceOnLinks v l = return r'.
Proof.
  induction l ; simpl ; intros v x IN ; [ contradict IN | ].
  destruct_or IN.
  {
    subst a.
    rewrite lem_Column_t_beq_refl.
    eauto.
  }
  {
    apply (IHl v) in IN ; auto ; clear IHl ; [].
    destruct IN as [r G].
    rewrite G.
    destruct a ; eauto ; [].
    destruct c.
    destruct ( Column_t_beq Column_reference_t_lglue v) ; eauto.
  }
Qed.

(* Used *)
Corollary in_getColumnReferenceOnLinks_right_2 :
  forall (l: list Link) v, 
      (exists (x:Table_t), In (Column_referenceLink {| Column_reference_t_lglue := v ;  Column_reference_t_rglue := x |}) l) -> 
      exists r' : Table_t,
        getColumn_referenceOnLinks v l = return r'.
Proof.
  intros. 
  destruct H.
  eapply in_getColumnReferenceOnLinks_right.
  exact H.
Qed.

(* Used *)
Lemma in_getColumnReferenceOnLinks_left :
  forall (l: list Link) col t, 
    getColumn_referenceOnLinks col l = return t -> 
    In (Column_referenceLink {| Column_reference_t_lglue := col ;  Column_reference_t_rglue := t |}) l  
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
    destruct(Column_t_beq Column_reference_t_lglue c) eqn:E.
    {
      PropUtils.inj IN.
      apply lem_Column_t_beq_id in E ; subst Column_reference_t_lglue.
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
    In (Column_referenceLink {| Column_reference_t_lglue := col ;  Column_reference_t_rglue := r |}) rm.(modelLinks) ->
    In (TableElement r) rm.(modelElements).

