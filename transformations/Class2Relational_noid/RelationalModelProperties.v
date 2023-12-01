
Require Import List.

Require Import core.utils.Utils.
Require Import core.Model.

From transformations.Class2Relational_noid
  Require Import Class2Relational ClassMetamodel RelationalMetamodel.


From transformations.Class2Relational_noid 
  Require C2RTactics.

Import Glue.

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
  + destruct a ; [ solve [auto] | ].
    destruct g.
    destruct (Column_t_beq left_glue c).
    * reflexivity.
    * auto.
Qed.

(* Used *)
Lemma in_getColumnReferenceOnLinks_right :
  forall (l: list Link) v (x:Table_t),
    In (Column_referenceLink {| left_glue := v ; right_glue := x |}) l -> 
      exists r' : Table_t,
        getColumn_referenceOnLinks v l = return r'.
Proof.
  induction l ; simpl ; intros v x IN ; [ contradict IN | ].
  destruct_or IN.
  {
    subst a.
    rewrite internal_Column_t_dec_lb ; eauto.
  }
  {
    apply (IHl v) in IN ; auto ; clear IHl ; [].
    destruct IN as [r G].
    rewrite G.
    destruct a ; eauto ; [].
    destruct g.
    destruct ( Column_t_beq left_glue v) ; eauto.
  }
Qed.

(* Used *)
Corollary in_getColumnReferenceOnLinks_right_2 :
  forall (l: list Link) v, 
      (exists (x:Table_t), In (Column_referenceLink {| 
                                   left_glue := v ; 
                                   right_glue := x |}) l) -> 
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
    In (Column_referenceLink {| left_glue := col ;  right_glue := t |}) l  
      .
Proof.
  induction l ; simpl ; intros c r IN ; [ discriminate IN | ].

  destruct a.
  { (* table *)
    apply IHl in IN.
    right ; exact IN.
  }    
  { (* columns *)
    destruct g.
    destruct(Column_t_beq left_glue c) eqn:E.
    {
      PropUtils.inj IN.
      apply internal_Column_t_dec_bl in E ; subst left_glue.
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
    In (Column_referenceLink {| left_glue := col ;  right_glue := r |}) rm.(modelLinks) ->
    In (TableElement r) rm.(modelElements).

