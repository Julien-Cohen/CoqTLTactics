Require Import List.

Require PropUtils.

(** Lists and Options *)

(** *** Options to lists *)


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


(** *** Lists of options to lists *)

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

(** *** Lifting lists of heterogeneous types *)

(** Consider a type A : C1 of t1 | C2 of t2. Here we consider we have lists of A and we want to deal with lists of t1 or lists of t2. *) 

Fixpoint lift_list {A} {B} (f:A->option B) (s:list A): list B :=
  match s with 
  | nil => nil
  | a::r => match f a with
            | Some v =>  v :: lift_list f  r
            | None => lift_list f r
            end
end.

Lemma lift_list_map_optiontolist {A} {B} :
  forall (f:A->option B)  s,
    lift_list f s = optionList2List (map f s).
Proof.
  induction s ; simpl.
  + reflexivity.
  + destruct (f a) ; simpl.
    - rewrite <- IHs. reflexivity.
    - exact IHs.
Qed.

Lemma In_lift {A} {B} :
  forall (f:A->option B) e s,
  In e (lift_list f s) <->
  exists v, f v = Some e /\ In v s.
Proof.
  intros f e s.
  split.  
  {
    rewrite lift_list_map_optiontolist.
    intro H.
    apply optionList2List_In in H.
    apply List.in_map_iff. exact H.
  }
  {
    intro H.
    rewrite lift_list_map_optiontolist.
    apply optionList2List_In_inv.
    apply in_map_iff.
    exact H.    
  }
Qed. 


Fixpoint find_lift {A} {B} (f1:A->option B) (f2: B->bool) (s:list A): option B :=
  match s with 
  | nil => None
  | a::r => match f1 a with
            | Some v => if f2 v then Some v else find_lift f1 f2 r
            | None => find_lift f1 f2 r
            end
end.


Lemma find_lift_filter_lift {A} {B} :
  forall (f1:A->option B) (f2:B->bool) s,
         find_lift f1 f2 s = find f2 (lift_list f1 s).
Proof.
  induction s.
  + reflexivity.
  + simpl.
    destruct (f1 a) ; simpl.
    - rewrite <- IHs. reflexivity.
    - exact IHs.
Qed.

Lemma find_some_poor {A} {B} : 
  forall (f1:A->option B) (f2:B->bool) s r,
    find_lift f1 f2 s = Some r ->
    List.In r (lift_list f1 s) /\ f2 r = true.
Proof.
  intros f1 f2 s r H.
  rewrite find_lift_filter_lift in H.
  apply List.find_some ; exact H.
Qed.

Lemma find_some {A} {B} : 
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
    rewrite find_lift_filter_lift.
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
    apply find_some in Heqo.
    destruct Heqo as (? & ? & ? & ?).
    apply H in H1 ; clear H.
    destruct H1 ; [ congruence | ].
    destruct H as ( ? & ? & ?).
    rewrite H0 in H. PropUtils.inj H.
    congruence.
  }
Qed.

Fixpoint filter_lift {A} {B} (f1:A->option B) (f2:B->bool)(s:list A): list B :=
  match s with 
  | nil => nil
  | a::r => match f1 a with
            | Some v =>  if f2 v then v :: filter_lift f1 f2 r else filter_lift f1 f2 r
            | None => filter_lift f1 f2 r
            end
end.

Lemma filter_lift_lift_list {A} {B} :
  forall (f1:A->option B) (f2:B->bool) s,
    filter_lift f1 f2 s = filter f2 (lift_list f1 s).
Proof.
  induction s ; simpl.
  + reflexivity.
  + destruct (f1 a) ; simpl.
    -  rewrite <- IHs. reflexivity.
    - exact IHs.
Qed.

Lemma filter_lift_in {A} {B} :
  forall (f1:A->option B) (f2:B->bool) s v,
    In v (filter_lift f1 f2 s) <-> (exists a, In a s /\ f1 a = Some v /\ f2 v = true).  
Proof.
  intros f1 f2 s v.
  rewrite filter_lift_lift_list.
  split ; intro H.
  {
    apply List.filter_In in H.
    destruct H as (H & H1).
    apply In_lift in H.
    destruct H as (? & ? & ?) ; eauto.
  }
  { 
    apply List.filter_In. 
    destruct H as (? & ? & ? & ?).
    split ; [ | assumption ].
    apply In_lift.
    eauto.
  }
Qed.
