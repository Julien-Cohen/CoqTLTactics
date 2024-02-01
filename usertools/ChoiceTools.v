From core 
  Require Syntax.

From core.utils 
  Require Import NotationUtils.


(** Tactics to specify an element in a list. *)

(** When we know which rule is the one we search, the following tactics help us to say it, in particular in the case we have an existential variable in the goal, as in [In ?r (Syntax.rules Class2Relational)]
(after use of [in_compute_trace_inv]). *)


(** First element in list (1 lemma, 2 tactics). *)
Lemma In_1 {A} :
      forall (e:A) s,
      (exists r, s = e :: r) -> In e s.
Proof.
  intros e s (r&E) ; subst s. 
  apply in_eq.
Qed.

Ltac first_in_list :=
  match goal with 
    [ |- In _ _ ] =>
      apply In_1 ; eexists ; reflexivity
  end.

Ltac first_rule :=
  match goal with 
    [ |- In _ (Syntax.rules _)] =>
      first_in_list
  end.


(** Second element in list (1 lemma, 2 tactics). *)
Lemma In_2 {A} :
      forall (e:A) s,
      (exists a r, s = a :: e :: r) -> In e s.
Proof.
  intros e s (a&r&E) ; subst s. 
  apply in_cons. apply in_eq.
Qed.

Ltac second_in_list :=
  match goal with 
    [ |- In _ _ ] =>
      apply In_2 ; eexists ; eexists ; reflexivity
  end.

Ltac second_rule :=
  match goal with 
    [ |- In _ (Syntax.rules _)] =>
      second_in_list
  end.

(* in rest *)
Lemma In_rest {A} :
      forall (e:A) s,
      (exists a r, s = a :: r /\ In e r) -> In e s.
Proof.
  intros e s (?&?&?&?). subst s. 
  apply in_cons. assumption.
Qed.

Ltac other_in_list :=
  match goal with 
    [ |- In _ _ ] =>
      apply In_rest ; eexists ; eexists ; split ; [reflexivity | ]
  end.


(** Switch/case on positions in lists. *)

Ltac rule_number n := 
  match n with 
    1 => first_rule 
  | 2 => second_rule 
end.

Ltac pattern_number n :=
  match n with 
    1 => first_in_list 
  | 2 => second_in_list 
  end.


(** On rule names *)

Local Ltac aux n :=
  match goal with 
    [ |- List.In _ (?e::?r)] => 
      match eval cbv in (String.eqb e.(Syntax.r_name) n) with 
      | true =>  ChoiceTools.first_in_list
      | false =>  ChoiceTools.other_in_list ; aux n
      end 
  | [ |- List.In _ List.nil ] =>  exfalso 
  end.

Ltac rule_named n := 
  match goal with 
    [ |- In _ ?s] => 
      match eval cbv in s with 
      | ?v => replace s with v ; [ | reflexivity ] ; aux n
      end 
  end.

