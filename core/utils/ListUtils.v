Require Import List.
Require Import EqNat.
Require Import core.utils.CpdtTactics.
Require Import Lia.

Require PropUtils BoolUtils OptionUtils.

Definition set_eq {A:Type} (t1 t2: list A) := incl t1 t2 /\ incl t2 t1.



Lemma incl_mutual_length_eq :
forall {A:Type} (t1 t2: list A),
  NoDup t1 -> NoDup t2 ->
  set_eq t1 t2 ->
    length t1 = length t2.
Proof.
intros A t1 t2 nd1 nd2 seteq.
unfold set_eq in seteq. destruct seteq as [incl1 incl2].
specialize (NoDup_incl_length nd1 incl1).
specialize (NoDup_incl_length nd2 incl2).
intros lt1 lt2.
lia.
Qed.

Lemma incl_filter_mutual :
forall {A:Type} t1 t2,
  set_eq t1 t2 ->
    forall f:A->bool, 
      set_eq (filter f t1) (filter f t2).
Proof.
unfold set_eq. intros. destruct H. unfold incl. revert H. revert H0. revert t2.
induction t1.
- split.
  + intros; specialize (H0 a). simpl in H1. inversion H1.
  + destruct t2; auto. specialize (H0 a). crush. 
- intros.
  induction t2.
  + split; specialize (H a); crush. 
  + split; intros; apply filter_In; apply filter_In in H1; split; crush.
Qed.

Lemma filter_mutual_length_eq :
forall {A:Type} (t1 t2: list A) f,
  NoDup t1 -> NoDup t2 ->
  set_eq t1 t2 ->
    length (filter f t1) = length (filter f t2).
Proof.
unfold set_eq.
intros A t1 t2 f nd1 nd2 incl.
apply (NoDup_filter f) in nd1.
apply (NoDup_filter f) in nd2.
specialize (incl_filter_mutual t1 t2 incl f). intros incl3. destruct incl3 as [incl3 incl4].
specialize (NoDup_incl_length nd1 incl3). intro lt1.
specialize (NoDup_incl_length nd2 incl4). intro lt2.
lia.
Qed.

Lemma set_eq_imply_nth_error_eq :
forall  {A:Type} (l1 l2: list A),
  NoDup l1 -> NoDup l2 ->
  set_eq l1 l2 -> 
    length l1 = 1 -> 
      nth_error l1 0 = nth_error l2 0.
Proof.
intros A l1 l2 nod1 nod2 seteq len.
specialize (incl_mutual_length_eq l1 l2 nod1 nod2 seteq). intro leneq. 
unfold set_eq in seteq.
destruct seteq as [incl1 incl2].
unfold incl in *.
unfold nth_error.
destruct l1 eqn:l1_ca.
+ crush.
+ destruct l2 eqn: l2_ca.
  ++ specialize (incl1 a). crush.
  ++ assert (l = nil) as l_nil. { simpl in len. apply length_zero_iff_nil. crush. }
     assert (l0 = nil) as l0_nil. { simpl in leneq. rewrite l_nil in leneq. simpl in leneq. apply length_zero_iff_nil. crush. }
     rewrite l_nil in incl1. rewrite l0_nil in incl1.
     specialize (incl1 a). crush.
Qed.

Inductive subseq {A: Type} : list A -> list A -> Prop :=
  | s_nil : forall l, subseq nil l
  | s_true : forall x xs ys, subseq xs ys -> subseq (x::xs) (x::ys)
  | s_false : forall y xs ys, subseq xs ys -> subseq xs (y::ys).

Definition listToListList {A : Type} (l : list A) : list (list A) :=
  map (fun e:A => e::nil) l.

Definition hasLength {A : Type} (l : list A) (n: nat): bool :=
  beq_nat (Datatypes.length l) n.


Definition singleton {A: Type} (a: A) : list A := a::nil.

Definition maybeSingleton {A: Type} (a : option A) : option (list A) :=
  option_map singleton a.


Ltac inv_maybeSingleton H :=
   match type of H with
   | maybeSingleton _ = Some _ =>
       unfold maybeSingleton in H ;
       unfold option_map in H ;
       OptionUtils.monadInv H
   end.
 

Definition singletons {A: Type} (l : list A) : list (list A) :=
  listToListList l.

Definition maybeSingletons {A: Type} (l : option (list A)) : option (list (list A)) :=
  option_map singletons l.

Definition tupleWith {A : Type} (l : list A) (e: list A) : list (list A) :=
  map (fun a:A => app (a::nil) e) l.

Definition maybeTuples {A: Type} (l : option (list A)) (e: list A) :=
  option_map (fun a => tupleWith a e) l.

Fixpoint mapWithIndex {A : Type} {B : Type} (f: nat -> A -> B) (n : nat) (l: list A) : list B :=
  match l with
  | nil => nil
  | a :: t => (f n a) :: (mapWithIndex f (S n) t)
  end.

Fixpoint zipWith {A : Type} {B : Type} {C : Type} (f: A -> B -> C) (la: list A) (lb: list B) : list C :=
  match la, lb with
  | ea::eas, eb::ebs => (f ea eb) :: (zipWith f eas ebs)
  | nil, _ => nil
  | _, nil => nil
  end.

Theorem in_flat_map_nil:
  forall {A B : Type} (f : A -> list B) (l : list A),
    (flat_map f l) = nil <-> (forall a: A, In a l -> f a = nil).
Proof.
  split.
  - intros Hnil a Hin.
    induction l.
    + contradiction.
    + simpl in Hnil. apply app_eq_nil in Hnil. destruct Hnil.
      inversion Hin; subst; auto.
  - intro H.
    induction l.
    + reflexivity.
    + simpl. rewrite H by (left; reflexivity). simpl.
      apply IHl. intros a0 H0. apply H. right. assumption.
Qed.

Lemma lem_in_flat_map_exists :
  forall (X Y:Type) (x:X) (y:Y) (f: X -> list Y),
    In y (f x) <-> (exists ys:list Y, f x = ys /\ In y ys).
Proof.
  intros.
  split; intro H.
  - exists (f x). split; auto.
  - destruct H as [_ [[] H']]. assumption.
Qed.

Theorem in_flat_map_exists:
  (forall (X Y:Type) (x:X) (y:Y) (f: X -> list Y) (B:Prop),
      (In y (f x) <-> B)) <->
  (forall (X Y:Type) (x:X) (y:Y) (f: X -> list Y) (B:Prop),
      (exists ys:list Y, f x = ys /\ In y ys) <-> B).
Proof.
  split; intros; specialize (H X Y x y f B); symmetry in H.
  - rewrite H. rewrite lem_in_flat_map_exists. reflexivity.
  - rewrite H. rewrite lem_in_flat_map_exists. reflexivity.
Qed.

Lemma flat_map_singleton {A} {B} (f:A->list B) (e:A):
  flat_map f (e::nil) = f e.
Proof.
  simpl.
  apply app_nil_r.
Qed.

Lemma map_flat_map {A} {B} {C}:
  forall  (f:B->C) (g:A-> list B) (s:list A),
     map f (flat_map g s) = List.flat_map (fun a => map f (g a)) s.
Proof.
  intros f g s.
  induction s ; simpl.
  reflexivity.
  rewrite List.map_app.
  f_equal ; auto.
Qed.


Lemma filter_nil:
    forall (A : Type) (f : A -> bool) (x : A) (l : list A),
      (filter f l) = nil <->  (forall a: A, In a l -> f a = false).
Proof.
  split; intros.
  - induction l.
    + destruct H0.
    + simpl in H. destruct (f a0) eqn:Ha0; [discriminate H | ].
      destruct H0; subst; auto.
  - induction l.
    + reflexivity.
    + simpl. destruct (f a) eqn:Ha.
      * rewrite H in Ha by (left; reflexivity). discriminate Ha.
      * apply IHl. intros. apply H. right. assumption.
Qed.

Lemma fold_right_list_invariant :
  forall (A : Type) (f : A -> list A -> list A) (la0: list A) (l: list A) (P : list A -> Prop),
  P la0 
  -> (forall (a' : A) (la' : list A), In a' l -> P la' -> P (f a' la'))
  -> P (fold_right f la0 l).
Proof.
  intros.
  induction l.
  - simpl. assumption.
  - simpl.
    apply H0.
    + simpl. left. reflexivity.
    + apply IHl.
      intros.
      apply H0.
      * simpl. right. assumption.
      * assumption.
Qed.

Lemma hd_error_In :  
  forall (A : Type) (a : A) (l : list A),
  hd_error l = Some a -> In a l.
Proof.
  intros.
  unfold hd_error in H.
  destruct l.
  - inversion H.
  - inversion H.
    simpl.
    left.
    reflexivity.
Qed.


Lemma in_not_nil {A} (a:A) s :
  In a s -> s <> nil.
Proof.
  intro H.  destruct s ; [ inversion H | congruence]. 
Qed.


Fixpoint count_occ_b {A} (f:A->A->bool) l e :=
  match l with 
  | nil => 0
  | a::r => (match f a e with true => 1  | false => 0 end) + count_occ_b f r e
  end.


Ltac incl_inv H :=
      match type of H with
      | incl nil _ =>
          clear H
      | incl (cons _ _) _ =>
          let IN := fresh H in
          apply List.incl_cons_inv in H ; 
          destruct H as [H IN] ;
          incl_inv IN (* recursion *)
      end.

Ltac unfold_In_cons H :=
  match type of H with
  | In _ (cons _ _) => 
      apply List.in_inv in H ;
      PropUtils.destruct_or H
  | In _ nil => inversion H
  end.


Lemma incl_singleton :
  forall {T} (a:T) b, List.In a b <-> incl (a::nil)  b .
Proof.
  intros ; split ; intro H.
  + unfold incl.
    intros e H2.
    repeat unfold_In_cons H2.
    subst. exact H.
  + incl_inv H. exact H. 
Qed.

Lemma in_singleton A (a:A) b : a = b <-> In a (b::nil).
  split. 
  + intro ; subst. apply in_eq.
  + simpl. intro H. PropUtils.remove_or_false H. auto.
Qed.

Set Implicit Arguments.
Scheme Equality for list.

Lemma list_beq_refl {A} : 
  forall (f:A->A->bool),
    (forall a, f a a = true) ->
    forall s, list_beq f s s = true.
Proof.
  intro f.
  induction s.
  reflexivity.
  simpl.
  rewrite H.
  rewrite IHs.
  reflexivity.
Qed.


Lemma list_beq_correct {A} : 
  forall (f:A->A->bool),
    (forall a b , f a b = true -> a = b) ->
    forall s1 s2 , list_beq f s1 s2 = true -> s1 = s2.
Proof.
  intros f H.
  induction s1 ; destruct s2 ; simpl ; intro E. 
  + reflexivity.
  + discriminate.
  + discriminate.
  + BoolUtils.destruct_conjunctions.
    f_equal ; auto.
Qed.

Lemma find_some_left {A}:
  forall f (l:list A) e,
    List.In e l ->
    f e = true ->
    (exists e', List.find f l = Some e').
Proof.
  intro f.
  induction l ; intros e IN F.
  + solve [inversion IN].
  + simpl in IN. destruct IN.
    - subst.
      exists e.
      simpl.
      rewrite F.
      reflexivity.
    - simpl.
      destruct (f a) ; eauto.
Qed.
