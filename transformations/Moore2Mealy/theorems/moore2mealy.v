(*
 * - change the definitions of moore and mealy machine for proofs
 * - write moore2mealy model transformation use a single function
 * - prove its correctness
 *)


Require Import List.
Require Import Coq.Arith.EqNat.
Require Import Bool.

Require PropUtils.

Module Moore.
(** * Moore machine *)

Record Node := { id : nat ; output : nat }.

(** Nodes are identified only by their identifiers. This is a relation of equivalence under the hypothesis that two different nodes cannot have the same identifier. *)
Definition beq_N n1 n2 :=
    Nat.eqb n1.(id) n2.(id).

(* Input pair: src node x input *)
Definition IPair : Set := Node * nat.

Definition beq_IPair p1 p2 :=
  match p1, p2 with
    (n1, i1), (n2, i2) => beq_N n1 n2 && Nat.eqb i1 i2
  end.

(* Transition rule of Moore machine: Input pair x trg node *)
Definition R :Set := IPair * Node.


(* Moore machine *)
Definition P := list R.

(* Search output node in Moore machine *)
Fixpoint search (p: P) (i: IPair) : option Node :=
  match p with
  | nil => None
  | (a, b) :: rs => 
      if beq_IPair a i 
      then 
        Some b 
      else 
        search rs i 
  end.

(* Semantics of Moore machine  *)
Fixpoint eval (p: P) (q: Node) (I: list nat) : option (list nat) :=
  match I with 
  | nil => Some nil
  | i :: I' => 
      
      match search p (q, i) with
      | None => None 
      | Some n => 
          match eval p n I' with 
          | Some res => Some (n.(output) :: res) 
          | None => None
          end 
      end
  end.

End Moore.

Module Mealy.
(** * Mealy machine *)

Record Node := { id : nat }. (* FIXME *)

Definition beq_N n1 n2 :=
    Nat.eqb n1.(id) n2.(id).

Definition IPair : Set := Node * nat.

Definition beq_IPair p1 p2 :=
  match p1, p2 with
    (n1, i1), (n2, i2) => beq_N n1 n2 && Nat.eqb i1 i2
  end.

(* Output pair: trg node x output *)
Definition OPair : Set := Node * nat. 


(* Transition rule of Mealy machine : Input pair x (trg node x output) *)
Definition R : Set := IPair * OPair.

(* Mealy machine *)
Definition P := list R.

(* Search output node *)
Fixpoint search (p: P) (i: IPair) : option OPair :=
  match p with
  | nil => None
  | (a, b) :: rs => 
      if beq_IPair a i 
      then 
        Some b 
      else 
        search rs i 
end.

(* Semantics of Mealy machine *)
Fixpoint eval (p: P) (q: Node) (I: list nat) : option (list nat) :=
  match I with 
  | nil => Some nil
  | i :: I' => 
      match search p (q, i) with
      | None => None
      | Some (a, b) => 
          match eval p a I' with
          | Some res =>Some (b :: res)
          | None => None
          end  
      end
  end.

End Mealy.

(** * Compiler *)

(* Compile Moore to Mealy *)
Definition compile_node (t:Moore.Node) : Mealy.Node :=
  {| Mealy.id := t.(Moore.id) |}. 

Definition compile_input_pair (i:Moore.IPair) : Mealy.IPair :=
  match i with 
    (node,input) => (compile_node node, input)
  end.

Definition compile_rule (t:Moore.R) : Mealy.R :=
  match t with
    (ipair, out_node) => (compile_input_pair ipair, (compile_node out_node, out_node.(Moore.output)))
  end.

Definition compile : Moore.P -> Mealy.P := 
  List.map compile_rule.

Lemma beq_node_stable :
  forall a b, 
    Moore.beq_N a b = Mealy.beq_N (compile_node a) (compile_node b).
Proof.
  intros ; reflexivity.
Qed.

Lemma beq_pair_stable : 
  forall a b, 
    Moore.beq_IPair a b =  Mealy.beq_IPair (compile_input_pair a) (compile_input_pair b).
Proof.
  destruct a ; destruct b. 
  reflexivity.
Qed.

(* Lemma: when input pair is not matched by moore machine, 
   it is also not matched by the compiled mealy machine *)
Lemma compile_s_correct_ca1:
  forall (p: Moore.P) i,
     Moore.search p i = None ->
     Mealy.search (compile p) (compile_input_pair i) = None.
Proof.
  intros p i s_of_P.
  induction p; simpl in s_of_P; simpl.
  - reflexivity.
  - destruct a. destruct n. simpl.
    rewrite <- beq_pair_stable.
    unfold compile_input_pair.
    destruct (Moore.beq_IPair i0 i) eqn:E.
    + discriminate s_of_P.
    + auto.
Qed.



(* Lemma: when input pair is matched by moore machine, 
   it is also matched by the compiled mealy machine 
   their matched outputs are also a correspondence *)
Lemma compile_s_correct_ca2:
  forall (p: Moore.P) i n,
    Moore.search p i = Some n ->
    Mealy.search (compile p) (compile_input_pair i) = Some (compile_node n, n.(Moore.output)).
Proof.
  intros p i n s_of_P.
  induction p; simpl in s_of_P; simpl.
  - discriminate s_of_P.
  - destruct a. destruct n. simpl.
    rewrite <- beq_pair_stable.
    destruct (Moore.beq_IPair i0 i).
    + destruct n0. PropUtils.inj s_of_P. reflexivity.
    + auto.
Qed.

(* Main theorem: compile is correct
   evaluation the same inputs produce the same output *)
Theorem compile_correct:
  forall (p: Moore.P) (q: Moore.Node) (I: list nat),
    Moore.eval p q I = Mealy.eval (compile p) (compile_node q) I.
Proof.
  intros p q I. revert q.
  induction I as [ | i I ].
  - (* I = nil *)
    intro ; reflexivity.
  - (* I = i :: I /\ P(I') *) 
    simpl. intro.
    fold (compile_input_pair (q,i)). 
    destruct (Moore.search p (q, i)) as [ n | ] eqn: s_of_P ; [ apply compile_s_correct_ca2 in s_of_P | apply compile_s_correct_ca1 in s_of_P] ; rewrite s_of_P.
    + (* input pair is matched by moore machine *)
      destruct n.
      rewrite IHI. reflexivity. 
    + (* input pair is not matched by moore machine *)
       reflexivity.
Qed.

