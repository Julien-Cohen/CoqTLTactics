Require Import List Multiset EqNat.

Definition doubleNat (a: nat) := 2 * a.

Definition double (l: list nat) : list nat :=
    map doubleNat l.

Definition l1 := 1 :: 1 :: 3 :: nil.

Compute double l1.

Definition set := list.



Definition set_in {A: Type} (s: set A) (a: A) := In a s.




Fixpoint fillMultiset (l: list nat) : multiset nat :=
match l with
    | nil => EmptyBag nat
    | a :: l' => munion (fillMultiset l') (SingletonBag _ eq_nat_decide a)
end.

Compute (fillMultiset l1).

Definition doubleMultiset (l: multiset nat) : multiset nat.
Proof.
Defined.

Definition a : 
  forall (a: nat) (ms1: multiset nat) (doubleMul), multiplicity ms1 a = multiplicity (doubleMultiset ms1) (2*a).
Defined.

