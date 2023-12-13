Require Import List.
Require Export core.utils.CpdtTactics.

Definition map_cons {A : Type} (a: A) (l : list (list A)) : list (list A) :=
  map (cons a) l.

Lemma In_map_cons : 
  forall (A: Type) (a b: A) (l: list (list A)) (sp: list A),
  In a sp -> In sp (map_cons b l) -> (a = b \/ (exists p, In a p /\ In p l)).
Proof.
  intros.
  unfold map_cons. 
  intros.
  apply in_map_iff in H0.
  destruct H0. destruct H0.
  rewrite <- H0 in H.
  apply in_inv in H.
  destruct H.
  - left. symmetry. assumption.
  - right. exists x. split. assumption. assumption.
Qed.

(** * prod_concat *)

(* TODO: rewrite by using cartesian product and map cons *)
Definition prod_cons {A : Type} (s1: list A) (s2 : list (list A)) : list (list A) :=
  flat_map (fun a:A => map (cons a) s2) s1.

Example prod_cons_test1:
  prod_cons (1::2::nil) ((3::4::nil)::(5::6::nil)::nil) = (1 :: 3 :: 4 :: nil) :: (1 :: 5 :: 6 :: nil) :: (2 :: 3 :: 4 :: nil) :: (2 :: 5 :: 6 :: nil) :: nil.
Proof. reflexivity. Qed.

Lemma prod_cons_nil :
  forall {A : Type} (s1: list A),
    prod_cons s1 nil = nil.
Proof.
  induction s1.
  - reflexivity.
  - simpl.
    exact IHs1.
Defined.

Lemma prod_cons_in :
  forall (T: Type) (s1: list T) (s2: list (list T)) (se: T) (sp3: list T),
    In sp3 (prod_cons s1 s2) -> In se sp3 ->
      (In se s1
       \/ ( exists (sp4 : list T), In sp4 s2 /\ In se sp4)).
Proof.
  induction s1; intros.
  - contradiction H.
  - simpl in H. apply in_app_or in H. destruct H.
    + induction s2; destruct H.
      * destruct H. destruct H0; [left | right].
        -- left. assumption.
        -- exists a0. split; [left | ]; auto.
      * apply IHs2 in H. destruct H; [left | right].
        -- assumption.
        -- destruct H as [sp4 [Hin Hin']].
           exists sp4. split; [right | ]; auto.
    + simpl. apply or_assoc. right. apply IHs1 with sp3; assumption.
Qed.
(* Note : The reverse property is false *)


Lemma prod_cons_in_inv :
  forall (T: Type) (se: T) (ss: list T) (s2: list T) (s3: list (list T)),
    (In se s2 /\ In ss s3) <-> In (se :: ss) (prod_cons s2 s3).
Proof.
  intros.
  generalize dependent se.
  generalize dependent ss.
  induction s2; intros ; simpl.
  - tauto. 
  - setoid_rewrite in_app_iff.
    setoid_rewrite <- IHs2 ; clear IHs2.
    setoid_rewrite in_map_iff.
    split.
    + intros (H1 & H2).
      destruct H1 ; [ subst | ].
      * left. eauto.
      * auto.
    + intro H ; destruct H.
      * destruct H as (? & H & ?).
        injection H ; intros ; subst.
        auto.
      * tauto.
Qed.

(** * cartesian_prod *)

Definition singleton_list {A :Type} (s: (list A)) : list (list A) :=
  map (fun a:A => a::nil) s.

(* Compute (singleton_list nil).
Compute (singleton_list (1::2::nil)). *)

Fixpoint cartesian_prod {A :Type} (s: list (list A)) : list (list A) :=
  match s with
  | nil => nil
  | a :: nil => singleton_list a
  | a :: c => flat_map (fun e => map (fun r => e::r) (cartesian_prod c)) a
  end.

(* Compute (cartesian_prod nil).
Compute (cartesian_prod ((3::4::nil) :: nil)).
Compute (cartesian_prod ((1::2::5::6::nil) :: (3::4::nil) :: nil)).
Compute (cartesian_prod ((1::2::nil) :: (3::4::nil) :: (5::6::nil) :: nil)). *)



(** * tuples_of_length_n *)

Fixpoint tuples_of_length_n {A :Type} (s1: list A) (n : nat) : list (list A) :=
  match n with
  | 0 => nil::nil
  | S n => prod_cons s1 (tuples_of_length_n s1 n)
  end.

(* Compute tuples_of_length_n (nil : list nat) 0. *)
(* Compute tuples_of_length_n (nil : list nat) 1. *)
(* Compute tuples_of_length_n (1::2::nil) 3. *)
(* Compute tuples_of_length_n (1::2::3::nil) 3. *)

Lemma tuples_of_length_n_nil :
  forall (T: Type) (n : nat),
    gt n 0 -> (tuples_of_length_n (nil : list T) n) = nil.
Proof.
  induction n.
  - simpl. intros. apply Arith_prebase.gt_irrefl_stt in H. contradiction H.
  - simpl. reflexivity.
Qed.

Lemma tuples_of_length_n_in :
    forall (T: Type) (n:nat) (si: list T) (tuple: list T) (se: T),
      In tuple (tuples_of_length_n si n) -> In se tuple -> In se si.
Proof.
  induction n.
  - intros. simpl in H. destruct H. rewrite <- H in H0. contradiction H0. contradiction H.
  - intros. simpl in H. apply prod_cons_in with (s1:=si) (se:=se) in H.
    destruct H.
    + assumption.
    + destruct  H. destruct H. apply IHn with (si:=si) (se:=se) in H.
      * assumption.
      * assumption.
    + assumption.
Qed.

Lemma tuples_of_length_n_incl_length :
  forall (T: Type) (n: nat) (sm: list T) (sp: list T),
    incl sp sm /\ length sp = n <-> In sp (tuples_of_length_n sm n).
Proof.
  induction n ; intros sm sp ; simpl.
  - setoid_rewrite length_zero_iff_nil. split.
    + intros (H & ?) ; subst ; left ; reflexivity.
    + intro H ; inversion_clear H ; [ subst | contradiction].
      split ; [ apply incl_nil_l | reflexivity ].
  - intros. simpl.
    destruct sp ; simpl.
    + setoid_rewrite in_flat_map.
      setoid_rewrite in_map_iff.
      split.
       * intros (_ & H) ; discriminate H. 
       * intros ( ? & ? & ? & ? & _). discriminate.
    + rewrite PeanoNat.Nat.succ_inj_wd.
      rewrite <- prod_cons_in_inv.
      rewrite <- IHn ; clear IHn.
      split.
      * intros (H1 & ?). apply List.incl_cons_inv in H1. tauto.
      * intros (? & ? & ?). 
        split ; [ | assumption].
        apply List.incl_cons ; assumption.
Qed.

(** * tuples_up_to_n *)

Fixpoint tuples_up_to_n {A : Type} (s1: list A) (n : nat) : list (list A) :=
  match n with
  | 0 => tuples_of_length_n s1 0
  | S n => tuples_of_length_n s1 (S n) ++ tuples_up_to_n s1 n
  end.

Lemma tuples_up_to_n_nil :
  forall (T: Type) (n : nat),
    (tuples_up_to_n (nil : list T) n) = nil::nil.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. assumption.
Qed.


Lemma tuples_up_to_n_In :
    forall (T: Type) (n: nat) (sm: list T) (sp: list T) (se: T),
      In sp (tuples_up_to_n sm n) -> In se sp -> In se sm.
Proof.
  induction n.
  - intros. simpl in H. destruct H. rewrite <- H in H0. contradiction H0. contradiction H.
  - intros. simpl in H. apply in_app_or in H. destruct H.
    + apply prod_cons_in with (s1:=sm) (se:=se) in H.
      * destruct H.
        ** assumption.
        ** destruct H. destruct H. apply tuples_of_length_n_in with (n:=n) (se:=se) in H.
           *** assumption.
           *** assumption.
      * assumption.
    + apply IHn with (se:=se) in H.
      * assumption.
      * assumption.
Qed.

Lemma tuples_up_to_n_incl :
    forall (T: Type) (n: nat) (sm: list T) (sp: list T),
      In sp (tuples_up_to_n sm n) -> incl sp sm.
Proof.
  induction n.
  - intros. simpl in H. destruct H. rewrite <- H. unfold incl. intros. contradiction H0. contradiction H.
  - intros. simpl in H. apply in_app_or in H. destruct H.
    + unfold incl. intros. apply prod_cons_in with (s1:=sm) (se:=a) in H.
      * destruct H.
        ** assumption.
        ** destruct H. destruct H. apply tuples_of_length_n_in with (n:=n) (se:=a) in H.
           *** assumption.
           *** assumption.
      * assumption.
    + unfold incl. intros. apply IHn in H. unfold incl in H.  apply H. assumption.
Qed.

Lemma tuples_up_to_n_incl_length :
    forall (T: Type) (n: nat) (sm: list T) (sp: list T),
      (incl sp sm /\ length sp <= n) <-> In sp (tuples_up_to_n sm n).
Proof.
  induction n; intros; simpl.
  - setoid_rewrite PeanoNat.Nat.le_0_r.
    setoid_rewrite length_zero_iff_nil.
    split.
    + intros (? & ?) ; subst ; auto.
    + intro H ; destruct H ; [ subst | contradiction].
      split ; [ apply incl_nil_l | reflexivity].
  - setoid_rewrite in_app_iff.
    setoid_rewrite <- IHn. clear IHn.
    setoid_rewrite in_flat_map.
    setoid_rewrite in_map_iff.
    setoid_rewrite <- tuples_of_length_n_incl_length.
    split.
    + intros (? & ?).
      destruct sp ; simpl.
      * right.
        split ; simpl ; auto with arith.
      * apply incl_cons_inv in H. destruct H. simpl in H0.
        apply le_S_n in H0.
        compare (length sp) n.
        { intro. subst. clear H0.
          
          left.  
          exists t.
          split ; [ assumption | ].
          exists sp.        
          split ; auto.
        }
        {
          intro.
          right.
          split.
          apply incl_cons ; assumption.
          apply Arith_prebase.lt_le_S_stt.
          apply PeanoNat.Nat.le_neq.
          split ; assumption.
        }
        
    + intro H.
      destruct H.
      * destruct H as (? & ? & ? & ? & ? & ?).
        subst.
        split ; auto.
        apply incl_cons ; assumption.
      * destruct H.
        split ;auto.
Qed.

Lemma tuples_up_to_n_size:
  forall A (a: list A) (sm: list A) n,
   In a (tuples_of_length_n sm n) -> length a = n.
Proof.
intros.
revert H.
revert a.
induction n.
- intros. simpl in H; crush.
- intros. simpl in H.
  apply in_flat_map in H.
  destruct H.
  destruct H.
  remember ((tuples_of_length_n sm n)) as l.
  apply in_map_iff in H0.
  destruct H0.
  destruct H0.
  specialize (IHn x0 H1).
  crush.
Qed.


Lemma tuple_length:
 forall {A: Type} (sp: list A) sm n,
  In sp (tuples_up_to_n sm n) -> length sp <= n.
Proof.
intros.
induction n; crush.
apply in_app_or in H.
destruct H.
- unfold prod_cons in H.
  apply in_flat_map in H.
  destruct H.
  destruct H.
  apply in_map_iff in H0.
  destruct H0.
  destruct H0.
  specialize (tuples_up_to_n_size A x0 sm n H1).
  intros.
  crush.
- crush.
Qed.
