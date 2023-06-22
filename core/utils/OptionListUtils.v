Require Import List.

Require PropUtils.

(** Lists and Options *)

Definition optionToList {A:Type} (o: option A) : list A :=
  match o with
  | Some a => a :: nil
  | None => nil
  end.

Lemma in_optionToList {A}:
  forall (a:A) b,
    In a (optionToList b) -> b = Some a.
Proof.
  intros a b IN.
  destruct b ; simpl in IN.
  + PropUtils.remove_or_false_auto.
    congruence.
  + contradiction.
Qed.

Lemma optionToList_map {A} {B}: 
  forall (f:A->B) a,
         optionToList (option_map f a) = map f (optionToList a).
Proof.
  intros.
  destruct a ; reflexivity.
Qed.

Definition optionListToList {A:Type} (o: option (list A)) : list A :=
  match o with
  | Some a => a
  | None => nil
  end.

Remark optionListToList_Some {A} :
  forall (a: list A), optionListToList (Some a) = a.
Proof.
  reflexivity.
Qed.

Lemma in_optionListToList {A} : forall (a:A) b,
    In a (optionListToList b) ->
    exists l, (b = Some l /\ In a l).
Proof.
  intros a b H.
  destruct b ; simpl in H ; [ | contradiction ]. 
  eauto.
Qed.

Ltac destruct_in_optionListToList H :=
  match type of H with
  | In _ (optionListToList ?E) =>
      let M := fresh "IN" in
      let l := fresh "l" in
      apply in_optionListToList in H;
      destruct H as (l, (H, M))
  end.

Definition optionList2List {A : Type} (l:list (option A)) : list A :=
  flat_map optionToList l.


Theorem optionListToList_In:
  forall (A:Type) (a: A) (l: option (list A)),
    In a (optionListToList l) ->
    l <> None.
Proof.
  intros.
  destruct_in_optionListToList H.
  subst.
  congruence.
Qed.


Theorem optionList2List_In :
  forall (A:Type) (a: A) (l: list (option A)), 
    In a (optionList2List l) ->
    In (Some a) l.
Proof.
  intros.
  induction l.
  - inversion H.
  - destruct a0.
    + destruct H.
      * left. rewrite H. reflexivity.
      * right. apply IHl. assumption.
    + right. apply IHl. assumption.
Qed.

Theorem optionList2List_In_inv :
  forall (A:Type) (a: A) (l: list (option A)),
    In (Some a) l ->
    In a (optionList2List l).
Proof.
  intros.
  induction l.
  - inversion H.
  - destruct a0.
    + destruct H.
      * rewrite H. left. reflexivity.
      * right. apply IHl. assumption.
    + apply IHl. destruct H.
      * inversion H.
      * assumption.
Qed.
