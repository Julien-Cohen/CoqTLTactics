Require Import String.
Require Import Bool.
Require Import Nat.
Require Import List.
Require Import Multiset.
Require Import ListSet.

Require Import core.utils.Utils.

Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Resolve.
Require Import core.Model.
Require Import core.TransformationConfiguration.

Require Import TT2BDD.TT.
Require Import TT2BDD.BDD.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Definition div_roundup (a b : nat) :=
  match modulo a b with
  | 0 => a / b
  | _ => (a / b) + 1
  end.

Definition times (lv : nat) := pow 2 lv.

Definition list_max (l:list nat) := fold_right max 0 l.

(* In this example, we try to explore that
   - we can write transformation without reflection
   - 
 *)

Definition guard (sp: list TTElem) := 
    match hd_error sp with
    | Some e => isColumn e
    | _ => false
    end.


Definition iter_col (sp: list TTElem) := 
  match hd_error sp with
  | Some e => match (Column_Level e) with
              | None => 0
              | Some lv => (times (lv-1)) 
              end
  | _ => 0
  end.
  
Definition oelem_name (sp: list TTElem) (iter: nat) := 
  match hd_error sp with
  | Some e => append (Column_Name e) (natToString iter)
  | _ => ""%string
  end.

Definition upper_level (sp: list TTElem) := 
  match hd_error sp with
  | Some e => match (Column_Level e) with
              | None => None
              | Some n => Some (n - 1)
              end 
  | _ => None
  end.

Definition locate (m: Model TTM) (lv: nat) := 
  find (fun e => match (Column_Level e) with
          | None => false
          | Some n => Nat.eqb n lv
          end) m.(modelElements).

Definition output_name (sp: list TTElem) := 
  match hd_error sp with
  | Some e => match (Row_Output e) with
              | None => ""%string
              | Some str => append "S_" str
              end 
  | _ => ""%string
  end.

Definition maxLv (m: Model TTM) := list_max (optionList2List (map Column_Level m.(modelElements))).

Fixpoint semantic (input: list nat) : nat :=
  match input with
  | nil => 0
  | a :: r => a * pow 2 ((length input)-1) + semantic r
  end.

(* Eval compute in semantic (0::0::1::nil). *)

#[export]
Instance TT2BDDConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration TTM BDDM.

Definition TT2BDD :=
  buildTransformation 1
  [ (* rules *)
    (buildRule "Columns2Tree"  
      (fun m sp => match sp with e :: _ => isColumn e | _ => false end)
      (fun m sp => return iter_col sp)
      [buildOutputPatternUnit "node"
          (fun i m col => return BuildBDDNode (oelem_name col i))
          (fun tls i m col output => 
            ulv <- (upper_level col);
            ucol <- locate m ulv;
            parent <- resolveIter tls "node" [ucol] ((div_roundup i 2)-1);
            return [BuildBDDEdge output parent])
      ]
    ) ;
    (buildRule "Row2Output"  
      (fun m sp => match sp with e :: _ => isRow e | _ => false end)  
      (fun m sp => return 1)
      [buildOutputPatternUnit "output"
          (fun i m sp => return BuildBDDNode (output_name sp))
          (fun tls i m sp output => 
            height <- Some (maxLv m);           (* get depth *)
            col <- locate m height;             (* get node of depth *)
            row <- hd_error sp;
            input <- (Row_Input row);
            parent <- resolveIter tls "node" [col] ((div_roundup (semantic input) 2)-1);   (* attach output to the corresponding leaf node*)
            return [BuildBDDEdge output parent])
      ]
    )
  ]. 
