Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Metamodel.

Scheme Equality for list.

(* Truth Table *)

Inductive TTElem := 
| BuildColumn :  
    (* name *) string ->
    (* level start at 1 *) nat ->
    TTElem
| BuildRow :
    (* inputs *) list nat ->
    (* output *) nat ->
    TTElem.

Lemma dec : forall (a b : TTElem), {a=b} + {a<>b}.
Proof.
  destruct a ; destruct b ; try (right ; intro ; discriminate).
  + compare n n0 ; intro ; [ subst | ].
    - destruct (string_dec s s0) ; [ subst ; left ; reflexivity | right ].
      contradict n ; congruence.  
    - right.  contradict n1.  congruence.
  + compare l l0.
    - intro ; subst.
      compare n n0 ; intro ; [ subst ; left | right].
      * reflexivity.
      * contradict n1 ; congruence.
    - intro. right. contradict n1 ; congruence.
    - decide equality.
Qed.

Definition TTEq (a b : TTElem) := 
    match a, b with
    | BuildColumn n1 l1, BuildColumn n2 l2 => String.eqb n1 n2 && Nat.eqb l1 l2
    | BuildRow lst1 n1, BuildRow lst2 n2 => list_beq nat Nat.eqb lst1 lst2 && Nat.eqb n1 n2
    | _,_ => false
    end.


Definition isColumn (e: TTElem) :=
    match e with
    | BuildColumn _ _ => true
    | _ => false
    end.

Definition isRow (e: TTElem) :=
    match e with
    | BuildRow _ _ => true
    | _ => false
    end.

Definition Column_Name (e : TTElem) := 
    match e with
    | BuildColumn n _ => n
    | _ => ""%string
    end.

Definition Column_Level (e : TTElem) := 
    match e with
    | BuildColumn _ lv => Some lv
    | _ => None
    end.

Definition Row_Input (e : TTElem) := 
    match e with
    | BuildRow input _ => Some input
    | _ => None
    end.

Definition Row_Output (e : TTElem) := 
    match e with
    | BuildRow _ output => Some (natToString output)
    | _ => None
    end.

Inductive TTRef :=
  unit. 

Definition TTM : Metamodel :=
  {| 
    ElementType := TTElem ;
    LinkType := TTRef ;
    elements_eq_dec := dec ;
  |}.


Definition evalTT (tt: Model TTM) (ins: list bool) : bool := true.

