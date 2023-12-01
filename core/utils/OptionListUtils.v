Require Import List.

Require PropUtils.
Require ListUtils.

(** Lists and Options *)

(** *** Options to lists *)


Definition optionToList {A:Type} (o: option A) : list A :=
  match o with
  | Some a => a :: nil
  | None => nil
  end.

Lemma in_optionToList {A}:
  forall (a:A) b,
    In a (optionToList b) <-> b = Some a.
Proof.
  intros a b. 
  destruct b ; simpl ; split ; intro H.
  + PropUtils.remove_or_false_auto.
    congruence.
  + left ; congruence.

  + contradiction.
  + discriminate.
Qed.

Lemma optionToList_map {A} {B}: 
  forall (f:A->B) a,
         optionToList (option_map f a) = map f (optionToList a).
Proof.
  intros.
  destruct a ; reflexivity.
Qed.


(** *** Options of lists to lists *)

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
    In a (optionListToList b) <->
    exists l, (b = Some l /\ In a l).
Proof.
  intros a b ; split ; intro H.
  { destruct b ; simpl in H ; [ | contradiction ]. eauto. }
  { destruct H as (l & E & H) ; subst b. simpl. exact H. }
Qed.

Ltac destruct_in_optionListToList H :=
  match type of H with
  | In _ (optionListToList ?E) =>
      let M := fresh "IN" in
      let l := fresh "l" in
      apply in_optionListToList in H;
      destruct H as (l, (H, M))
  end.


(** *** Lists of options to lists *)

Definition optionList2List {A : Type} (l:list (option A)) : list A :=
  List.fold_right (fun e r => match e with None => r | Some a => a :: r end) nil l.


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

Theorem optionList2List_In_eq :
  forall (A:Type) (a: A) (l: list (option A)),
    In (Some a) l <->
    In a (optionList2List l).
Proof.
  intros ; split ; intro.
  + apply optionList2List_In_inv ; assumption.
  + apply optionList2List_In ; assumption.
Qed.

(** *** Lifting lists of heterogeneous types *)

(** Consider a type A : C1 of t1 | C2 of t2. Here we consider we have lists of A and we want to deal with lists of t1 or lists of t2. *) 

Definition lift_list {A} {B} (f:A->option B) (s:list A): list B :=
  optionList2List (List.map f s).


Lemma In_lift {A} {B} :
  forall (f:A->option B) e s,
  In e (lift_list f s) <->
  exists v, f v = Some e /\ In v s.
Proof.
  unfold lift_list.
  setoid_rewrite <- optionList2List_In_eq.
  setoid_rewrite List.in_map_iff. tauto.
Qed. 


Definition find_lift {A} {B} (f1:A->option B) (f2: B->bool) (s:list A): option B :=
  List.find f2 (optionList2List (List.map f1 s)).


Lemma find_some_poor {A} {B} : 
  forall (f1:A->option B) (f2:B->bool) s r,
    find_lift f1 f2 s = Some r ->
    List.In r (lift_list f1 s) /\ f2 r = true.
Proof.
  intros f1 f2 s r H.
  apply List.find_some. exact H.
Qed.

Lemma find_lift_some {A} {B} : 
  forall (f1:A->option B) (f2:B->bool) s r,
    find_lift f1 f2 s = Some r ->
    exists v, f1 v = Some r /\ In v s /\ f2 r = true.
Proof.
  intros f1 f2 s r H.
  apply find_some_poor in H.
  destruct H as [H1 H2].
  apply In_lift in H1.
  destruct H1 as (v & (? & ?)) ; eauto.
Qed.

Lemma find_none {A} {B} : 
  forall (f1:A->option B) (f2:B->bool) s,
    find_lift f1 f2 s = None <->
    forall x, List.In x s -> (f1 x = None \/ (exists v, f1 x = Some v /\ f2 v = false)).
Proof.
  intros f1 f2 s.
  split.
  { 
    intro H. 
    intros x IN.
    destruct (f1 x) eqn:? ; [ | solve [auto] ].
    right.
    exists b.
    split ; [ reflexivity | ].
    eapply List.find_none ; eauto.
    apply In_lift ; eauto.
  }
  {
    intro H.
    match goal with [ |- ?F = None] => destruct F eqn:? end ; [ exfalso | reflexivity ].
    apply find_lift_some in Heqo.
    destruct Heqo as (? & ? & ? & ?).
    apply H in H1 ; clear H.
    destruct H1 ; [ congruence | ].
    destruct H as ( ? & ? & ?).
    rewrite H0 in H. PropUtils.inj H.
    congruence.
  }
Qed.



Lemma in_find_lift {A} {B} e a (l:list A) (f1:A->option B) (f2:B->bool) :
  ListUtils.discriminating_predicate (fun x => f2 x = true) (OptionListUtils.lift_list f1 l) ->
  f1 e = Some a ->
  f2 a = true ->
  List.In e l ->
  OptionListUtils.find_lift f1 f2 l = Some a.
Proof.
  intros.
  apply ListUtils.in_find ; auto.
  apply In_lift ; eauto.
Qed.

Definition filter_lift {A} {B} (f1:A->option B) (f2:B->bool)(s:list A): list B := filter f2 (lift_list f1 s).

Lemma filter_lift_in {A} {B} :
  forall (f1:A->option B) (f2:B->bool) s v,
    In v (filter_lift f1 f2 s) <-> (exists a, In a s /\ f1 a = Some v /\ f2 v = true).  
Proof.
  intros f1 f2 s v.
  unfold filter_lift.
  rewrite List.filter_In.
  rewrite In_lift. 
  split ; intro H.
  { destruct H as ((?&?&?) & ?) ; eauto. }
  { destruct H as (? & ? & ? & ?) ; eauto. }
Qed.
