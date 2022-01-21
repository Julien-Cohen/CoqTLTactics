
(********************************************************************
	@name Coq declarations for metamodel: <TT>
	@date 2019/06/10 19:46:45
	@description Automatically generated by Ecore2Coq transformation.
 ********************************************************************)

(* Coq libraries *)
Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.

Require Import Coq.Logic.Eqdep_dec.


(* Base types *)

(* Check: flatten attribute in inheritence hierachy *)

Inductive TruthTable : Set :=
  BuildTruthTable :
  (* id *) string ->
  (* location *) string ->
  (* name *) string ->
  TruthTable.

Inductive Row : Set :=
  BuildRow :
  (* id *) string ->
  (* location *) string ->
  Row.
  
Inductive Cell : Set :=
  BuildCell :
  (* id *) string ->
  (* location *) string ->
  (* value *) bool ->
  Cell.

Inductive InputPort : Set :=
  BuildInputPort :
  (* id *) string ->
  (* location *) string ->
  (* name *) string ->
  InputPort.
  
Inductive OutputPort : Set :=
  BuildOutputPort :
  (* id *) string ->
  (* location *) string ->
  (* name *) string ->
  OutputPort.

(* Port-types *)
Inductive Port_EClass : Set :=
  | InputPortEClass
  | OutputPortEClass
.

Definition Port_getTypeByEClass (arg : Port_EClass) : Set :=
  match arg with
    | InputPortEClass => InputPort
    | OutputPortEClass => OutputPort
  end.

(* Check: abstract class as predicated constructor *)
Inductive Port : Set :=
  | Build_Abstract_Port : 
    forall (arg: Port_EClass), 
      (Port_getTypeByEClass arg) -> Port.

(* AbstractState-types *)
Inductive LocatedElement_EClass : Set :=
  | TruthTableEClass
  | RowEClass
  | CellEClass
  | PortEClass
.

(* Check: deep inheritence hierachy can be handeled *)
Definition LocatedElement_getTypeByEClass (hsec_arg : LocatedElement_EClass) : Set :=
  match hsec_arg with
  | TruthTableEClass => TruthTable
  | RowEClass => Row
  | CellEClass => Cell
  | PortEClass => Port
  end.

(* Check: parent class might be instaniateable, solve by alternative constructors *)
Inductive LocatedElement : Set :=
| Build_Concrete_LocatedElement :
  (* id *) string ->
  (* location *) string ->
  LocatedElement
| Build_Abstract_LocatedElement : 
    forall (arg: LocatedElement_EClass), 
      (LocatedElement_getTypeByEClass arg) -> LocatedElement.

(* Check: multiple inheritence 

   The idea is have separate set of eclass for each parent class, 

   rename if overlapped

   This delegate a complex job for the model generator

   to flatten element/reference that corresponds to multi-inheritence

Inductive NamedElement_EClass : Set :=
  | TruthTableEClass2
  | InputPortEClass2
.

Definition NamedElement_getTypeByEClass (hsec_arg : NamedElement_EClass) : Set :=
  match hsec_arg with
  | TruthTableEClass2 => TruthTable
  | InputPortEClass2 => InputPort
  end.

*)

Inductive TruthTablePorts : Set :=
   BuildTruthTablePorts :
   TruthTable ->
   list Port ->
   TruthTablePorts.

Inductive TruthTableRows : Set :=
   BuildTruthTableRows :
   TruthTable ->
   list Row ->
   TruthTableRows.

Inductive PortOwner : Set :=
   BuildPortOwner :
   Port ->
   TruthTable ->
   PortOwner.

(* Check: relationship on children-class does not affect siblings 
          because each relationship is pinpoint on the exact sub-classes *)
Inductive PortCells : Set :=
   BuildPortCells :
   Port ->
   list Cell ->
   PortCells.

Inductive RowOwner : Set :=
   BuildRowOwner :
   Row ->
   TruthTable ->
   RowOwner.

Inductive RowCells : Set :=
   BuildRowCells :
   Row ->
   list Cell ->
   RowCells.

Inductive CellOwner : Set :=
   BuildCellOwner :
   Cell ->
   Row ->
   CellOwner.

Inductive CellPort : Set :=
   BuildCellPort :
   Cell ->
   Port ->
   CellPort.



(* Accessors *)


Definition TruthTable_getLocation (t : TruthTable) : string :=
  match t with BuildTruthTable  id location name  => location end.
Definition TruthTable_getId (t : TruthTable) : string :=
  match t with BuildTruthTable id location name  => id end.
Definition TruthTable_getName (t : TruthTable) : string :=
  match t with BuildTruthTable id location name  => name end.
 

Definition InputPort_getLocation (i : InputPort) : string :=
  match i with BuildInputPort  id location name  => location end.
Definition InputPort_getId (i : InputPort) : string :=
  match i with BuildInputPort  id location name  => id end.
Definition InputPort_getName (i : InputPort) : string :=
  match i with BuildInputPort  id location name  => name end.

Definition OutputPort_getLocation (o : OutputPort) : string :=
  match o with BuildOutputPort  id location name   => location end.
Definition OutputPort_getId (o : OutputPort) : string :=
  match o with BuildOutputPort  id location name   => id end.
Definition OutputPort_getName (o : OutputPort) : string :=
  match o with BuildOutputPort  id location name   => name end.

Definition Row_getLocation (r : Row) : string :=
  match r with BuildRow  id  location => location end.
Definition Row_getId (r : Row) : string :=
  match r with BuildRow  id location => id end.
 
Definition Cell_getLocation (c : Cell) : string :=
  match c with BuildCell  id location value  => location end.
Definition Cell_getId (c : Cell) : string :=
  match c with BuildCell  id location value  => id end.
Definition Cell_getValue (c : Cell) : bool :=
  match c with BuildCell  id location value  => value end.


Definition Port_getLocation (p : Port) : string :=
  match p with 
    | Build_Abstract_Port InputPortEClass (BuildInputPort  id location name)  => location 
    | Build_Abstract_Port OutputPortEClass (BuildOutputPort  id location name) => location
  end.
Definition Port_getId (p : Port) : string :=
  match p with 
    | Build_Abstract_Port InputPortEClass (BuildInputPort  id location name)  => id 
    | Build_Abstract_Port OutputPortEClass (BuildOutputPort  id location name) => id
  end.
Definition Port_getName (p : Port) : string :=
  match p with 
    | Build_Abstract_Port InputPortEClass (BuildInputPort  id location name)  => name 
    | Build_Abstract_Port OutputPortEClass (BuildOutputPort  id location name) => name
  end.

Definition LocatedElement_getId (l : LocatedElement) : string :=
  match l with 
    | Build_Concrete_LocatedElement id location  => id 
    | Build_Abstract_LocatedElement TruthTableEClass (BuildTruthTable  id location name) => id
    | Build_Abstract_LocatedElement RowEClass (BuildRow  id location) => id
    | Build_Abstract_LocatedElement CellEClass (BuildCell  id location value) => id
    | Build_Abstract_LocatedElement PortEClass p => Port_getId p
  end.
Definition LocatedElement_getLocation (l : LocatedElement) : string :=
  match l with 
    | Build_Concrete_LocatedElement id location  => location 
    | Build_Abstract_LocatedElement TruthTableEClass (BuildTruthTable  id location name) => location
    | Build_Abstract_LocatedElement RowEClass (BuildRow  id location) => location
    | Build_Abstract_LocatedElement CellEClass (BuildCell  id location value) => location
    | Build_Abstract_LocatedElement PortEClass p => Port_getLocation p
  end.


(* Meta-types *)

Inductive TTMetamodel_EClass : Set :=
  | LocatedElementEClass
.

Definition TTMetamodel_getTypeByEClass (ttec_arg : TTMetamodel_EClass) : Set :=
  match ttec_arg with
    | LocatedElementEClass => LocatedElement
  end.

Inductive TTMetamodel_EReference : Set :=
| TruthTablePortsEReference
| TruthTableRowsEReference
| PortOwnerEReference
| PortCellsEReference
| RowOwnerEReference
| RowCellsEReference
| CellOwnerEReference
| CellPortEReference
.

Definition TTMetamodel_getTypeByEReference (tter_arg : TTMetamodel_EReference) : Set :=
  match tter_arg with
| TruthTablePortsEReference => TruthTablePorts
| TruthTableRowsEReference => TruthTableRows
| PortOwnerEReference => PortOwner
| PortCellsEReference => PortCells
| RowOwnerEReference => RowOwner
| RowCellsEReference => RowCells
| CellOwnerEReference => CellOwner
| CellPortEReference => CellPort
  end.


(* Generic types *)

Inductive TTMetamodel_EObject : Set :=
 | Build_TTMetamodel_EObject : 
    forall (ttec_arg: TTMetamodel_EClass), (TTMetamodel_getTypeByEClass ttec_arg) -> TTMetamodel_EObject.

Inductive TTMetamodel_ELink : Set :=
 | Build_TTMetamodel_ELink : 
    forall (tter_arg:TTMetamodel_EReference), (TTMetamodel_getTypeByEReference tter_arg) -> TTMetamodel_ELink.

(* Reflective functions *)

Lemma TTMetamodel_eqEClass_dec : 
 forall (ttec_arg1:TTMetamodel_EClass) (ttec_arg2:TTMetamodel_EClass), { ttec_arg1 = ttec_arg2 } + { ttec_arg1 <> ttec_arg2 }.
Proof. repeat decide equality. Defined.

Lemma TTMetamodel_eqEReference_dec : 
 forall (tter_arg1:TTMetamodel_EReference) (tter_arg2:TTMetamodel_EReference), { tter_arg1 = tter_arg2 } + { tter_arg1 <> tter_arg2 }.
Proof. repeat decide equality. Defined.

Definition TTMetamodel_getEClass (tteo_arg : TTMetamodel_EObject) : TTMetamodel_EClass :=
   match tteo_arg with
  | (Build_TTMetamodel_EObject tteo_arg _) => tteo_arg
   end.

Definition TTMetamodel_getEReference (ttel_arg : TTMetamodel_ELink) : TTMetamodel_EReference :=
   match ttel_arg with
  | (Build_TTMetamodel_ELink ttel_arg _) => ttel_arg
   end.

Definition TTMetamodel_instanceOfEClass (ttec_arg: TTMetamodel_EClass) (tteo_arg : TTMetamodel_EObject): bool :=
  if TTMetamodel_eqEClass_dec (TTMetamodel_getEClass tteo_arg) ttec_arg then true else false.

Definition TTMetamodel_instanceOfEReference (tter_arg: TTMetamodel_EReference) (ttel_arg : TTMetamodel_ELink): bool :=
  if TTMetamodel_eqEReference_dec (TTMetamodel_getEReference ttel_arg) tter_arg then true else false.


Definition TTMetamodel_toEClass (ttec_arg : TTMetamodel_EClass) (tteo_arg : TTMetamodel_EObject) : option (TTMetamodel_getTypeByEClass ttec_arg).
Proof.
  destruct tteo_arg as [arg1 arg2].
  destruct (TTMetamodel_eqEClass_dec arg1 ttec_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
    exact (Some arg2).
  - exact None.
Defined.

Definition TTMetamodel_toEReference (tter_arg : TTMetamodel_EReference) (ttel_arg : TTMetamodel_ELink) : option (TTMetamodel_getTypeByEReference tter_arg).
Proof.
  destruct ttel_arg as [arg1 arg2].
  destruct (TTMetamodel_eqEReference_dec arg1 tter_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
  	exact (Some arg2).
  - exact None.
Defined.

Lemma TTMetamodel_eqPortEClass_dec : 
 forall (ttec_arg1:Port_EClass) (ttec_arg2:Port_EClass), { ttec_arg1 = ttec_arg2 } + { ttec_arg1 <> ttec_arg2 }.
Proof. repeat decide equality. Defined.

Lemma TTMetamodel_eqLocatedElementEClass_dec : 
 forall (ttec_arg1:LocatedElement_EClass) (ttec_arg2:LocatedElement_EClass), { ttec_arg1 = ttec_arg2 } + { ttec_arg1 <> ttec_arg2 }.
Proof. repeat decide equality. Defined.

(* Generic functions *)
Definition TTMetamodel_toEObjectFromLocatedElement (lo_arg :LocatedElement) : TTMetamodel_EObject :=
  (Build_TTMetamodel_EObject LocatedElementEClass lo_arg).
Coercion TTMetamodel_toEObjectFromLocatedElement : LocatedElement >-> TTMetamodel_EObject.

(** Metamodel Type Class Instaniation **)
Definition TTMetamodel_toEObject (tteo_arg : TTMetamodel_EObject) : TTMetamodel_EObject := tteo_arg.
Definition TTMetamodel_toELink (ttel_arg : TTMetamodel_ELink) : TTMetamodel_ELink := ttel_arg.
Definition TTModel := Model TTMetamodel_EObject TTMetamodel_ELink.

Definition TTMetamodel_toEObjectOfEClass (ttec_arg: TTMetamodel_EClass) (t: TTMetamodel_getTypeByEClass ttec_arg) : TTMetamodel_EObject :=
  (Build_TTMetamodel_EObject ttec_arg t).

Definition TTMetamodel_toELinkOfEReference (tter_arg: TTMetamodel_EReference) (t: TTMetamodel_getTypeByEReference tter_arg) : TTMetamodel_ELink :=
		  (Build_TTMetamodel_ELink tter_arg t).


(* Accessors on model *)
(* Equality for Types *)

Definition beq_TruthTable (tr_arg1 : TruthTable) (tr_arg2 : TruthTable) : bool :=
 ( beq_string (TruthTable_getLocation tr_arg1) (TruthTable_getLocation tr_arg2) ) &&
 ( beq_string (TruthTable_getId tr_arg1) (TruthTable_getId tr_arg2) ) &&
 ( beq_string (TruthTable_getName tr_arg1) (TruthTable_getName tr_arg2) )
.

Definition beq_InputPort (in_arg1 : InputPort) (in_arg2 : InputPort) : bool :=
( beq_string (InputPort_getLocation in_arg1) (InputPort_getLocation in_arg2) ) &&
( beq_string (InputPort_getId in_arg1) (InputPort_getId in_arg2) ) &&
( beq_string (InputPort_getName in_arg1) (InputPort_getName in_arg2) )
.

Definition beq_OutputPort (ou_arg1 : OutputPort) (ou_arg2 : OutputPort) : bool :=
( beq_string (OutputPort_getLocation ou_arg1) (OutputPort_getLocation ou_arg2) ) &&
( beq_string (OutputPort_getId ou_arg1) (OutputPort_getId ou_arg2) ) &&
( beq_string (OutputPort_getName ou_arg1) (OutputPort_getName ou_arg2) )
.

Definition beq_Port (po_arg1 : Port) (po_arg2 : Port) : bool :=
  match po_arg1, po_arg2 with
  | Build_Abstract_Port InputPortEClass i1, Build_Abstract_Port InputPortEClass i2 =>
      ( beq_InputPort i1 i2)
  | Build_Abstract_Port OutputPortEClass o1, Build_Abstract_Port OutputPortEClass o2 =>
      ( beq_OutputPort o1 o2) 
  | _,_ => false
  end.

Definition beq_Row (ro_arg1 : Row) (ro_arg2 : Row) : bool :=
beq_string (Row_getLocation ro_arg1) (Row_getLocation ro_arg2) &&
beq_string (Row_getId ro_arg1) (Row_getId ro_arg2)
.

Definition beq_Cell (ce_arg1 : Cell) (ce_arg2 : Cell) : bool :=
beq_string (Cell_getLocation ce_arg1) (Cell_getLocation ce_arg2) &&
beq_string (Cell_getId ce_arg1) (Cell_getId ce_arg2) &&
( beq_bool (Cell_getValue ce_arg1) (Cell_getValue ce_arg2) )
.

(* Check: equality of locatedElement, it is used in an important place of type class instantiation *)

Definition beq_LocatedElement (lo_arg1 : LocatedElement) (lo_arg2 : LocatedElement) : bool :=
  match lo_arg1, lo_arg2 with
  | Build_Concrete_LocatedElement id1 location1, Build_Concrete_LocatedElement id2 location2 => 
      ( beq_string location1 location2 ) && ( beq_string id1 id2 )
  | Build_Abstract_LocatedElement TruthTableEClass tt1, Build_Abstract_LocatedElement TruthTableEClass tt2 =>
      ( beq_TruthTable tt1 tt2)
  | Build_Abstract_LocatedElement PortEClass p1, Build_Abstract_LocatedElement PortEClass p2 =>
      ( beq_Port p1 p2)
  | Build_Abstract_LocatedElement RowEClass r1, Build_Abstract_LocatedElement RowEClass r2 =>
      ( beq_Row r1 r2)
  | Build_Abstract_LocatedElement CellEClass c1, Build_Abstract_LocatedElement CellEClass c2 =>
      ( beq_Cell c1 c2) 
  | _,_ => false
  end.

Definition TTMetamodel_Port_DownCast (ttec_arg : Port_EClass) (tteo_arg : Port) : option (Port_getTypeByEClass ttec_arg).
Proof.
  destruct tteo_arg as [arg1 arg2].
  destruct (TTMetamodel_eqPortEClass_dec arg1 ttec_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
    exact (Some arg2).
  - exact None.
Defined.

Definition TTMetamodel_LocatedElement_DownCast (ttec_arg : LocatedElement_EClass) (tteo_arg : LocatedElement) : option (LocatedElement_getTypeByEClass ttec_arg).
Proof.
  destruct tteo_arg.
  - exact None.
  - destruct (TTMetamodel_eqLocatedElementEClass_dec arg ttec_arg) as [e|] eqn:dec_case.
    -- rewrite e in l.
       exact (Some l).
    -- exact None.
Defined.

(* Check the model is a bit wired, where the element is wrapped around parent classes (e.g. BuildPort inputElcass p),
         and the link is not wrapped (e.g. just p) *)

Fixpoint TruthTable_getPortsOnLinks (tr_arg : TruthTable) (l : list TTMetamodel_ELink) : option (list Port) :=
match l with
| (Build_TTMetamodel_ELink TruthTablePortsEReference (BuildTruthTablePorts TruthTable_ctr ports_ctr)) :: l' => 
	  if beq_TruthTable TruthTable_ctr tr_arg then Some ports_ctr else TruthTable_getPortsOnLinks tr_arg l'
| _ :: l' => TruthTable_getPortsOnLinks tr_arg l'
| nil => None
end.
Definition TruthTable_getPorts (tr_arg : TruthTable) (m : TTModel) : option (list Port) :=
  TruthTable_getPortsOnLinks tr_arg (@allModelLinks _ _ m).
Fixpoint TruthTable_getRowsOnLinks (tr_arg : TruthTable) (l : list TTMetamodel_ELink) : option (list Row) :=
match l with
| (Build_TTMetamodel_ELink TruthTableRowsEReference (BuildTruthTableRows TruthTable_ctr rows_ctr)) :: l' => 
	  if beq_TruthTable TruthTable_ctr tr_arg then Some rows_ctr else TruthTable_getRowsOnLinks tr_arg l'
| _ :: l' => TruthTable_getRowsOnLinks tr_arg l'
| nil => None
end.

Definition TruthTable_getRows (tr_arg : TruthTable) (m : TTModel) : option (list Row) :=
  TruthTable_getRowsOnLinks tr_arg (@allModelLinks _ _ m).

Fixpoint Port_getOwnerOnLinks (po_arg : Port) (l : list TTMetamodel_ELink) : option (TruthTable) :=
match l with
| (Build_TTMetamodel_ELink PortOwnerEReference (BuildPortOwner Port_ctr owner_ctr)) :: l' => 
	  if beq_Port Port_ctr po_arg then Some owner_ctr else Port_getOwnerOnLinks po_arg l'
| _ :: l' => Port_getOwnerOnLinks po_arg l'
| nil => None
end.

Definition Port_getOwner (po_arg : Port) (m : TTModel) : option (TruthTable) :=
  Port_getOwnerOnLinks po_arg (@allModelLinks _ _ m).
Fixpoint Port_getCellsOnLinks (po_arg : Port) (l : list TTMetamodel_ELink) : option (list Cell) :=
match l with
| (Build_TTMetamodel_ELink PortCellsEReference (BuildPortCells Port_ctr cells_ctr)) :: l' => 
	  if beq_Port Port_ctr po_arg then Some cells_ctr else Port_getCellsOnLinks po_arg l'
| _ :: l' => Port_getCellsOnLinks po_arg l'
| nil => None
end.

Definition Port_getCells (po_arg : Port) (m : TTModel) : option (list Cell) :=
  Port_getCellsOnLinks po_arg (@allModelLinks _ _ m).



Fixpoint Row_getOwnerOnLinks (ro_arg : Row) (l : list TTMetamodel_ELink) : option (TruthTable) :=
match l with
| (Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner Row_ctr owner_ctr)) :: l' => 
	  if beq_Row Row_ctr ro_arg then Some owner_ctr else Row_getOwnerOnLinks ro_arg l'
| _ :: l' => Row_getOwnerOnLinks ro_arg l'
| nil => None
end.

Definition Row_getOwner (ro_arg : Row) (m : TTModel) : option (TruthTable) :=
  Row_getOwnerOnLinks ro_arg (@allModelLinks _ _ m).
Fixpoint Row_getCellsOnLinks (ro_arg : Row) (l : list TTMetamodel_ELink) : option (list Cell) :=
match l with
| (Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells Row_ctr cells_ctr)) :: l' => 
	  if beq_Row Row_ctr ro_arg then Some cells_ctr else Row_getCellsOnLinks ro_arg l'
| _ :: l' => Row_getCellsOnLinks ro_arg l'
| nil => None
end.

Definition Row_getCells (ro_arg : Row) (m : TTModel) : option (list Cell) :=
  Row_getCellsOnLinks ro_arg (@allModelLinks _ _ m).

Fixpoint Cell_getOwnerOnLinks (ce_arg : Cell) (l : list TTMetamodel_ELink) : option (Row) :=
match l with
| (Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner Cell_ctr owner_ctr)) :: l' => 
	  if beq_Cell Cell_ctr ce_arg then Some owner_ctr else Cell_getOwnerOnLinks ce_arg l'
| _ :: l' => Cell_getOwnerOnLinks ce_arg l'
| nil => None
end.

Definition Cell_getOwner (ce_arg : Cell) (m : TTModel) : option (Row) :=
  Cell_getOwnerOnLinks ce_arg (@allModelLinks _ _ m).
Fixpoint Cell_getPortOnLinks (ce_arg : Cell) (l : list TTMetamodel_ELink) : option (Port) :=
match l with
| (Build_TTMetamodel_ELink CellPortEReference (BuildCellPort Cell_ctr port_ctr)) :: l' => 
	  if beq_Cell Cell_ctr ce_arg then Some port_ctr else Cell_getPortOnLinks ce_arg l'
| _ :: l' => Cell_getPortOnLinks ce_arg l'
| nil => None
end.

Definition Cell_getPort (ce_arg : Cell) (m : TTModel) : option (Port) :=
  Cell_getPortOnLinks ce_arg (@allModelLinks _ _ m).

Definition beq_TTMetamodel_Object (c1 : TTMetamodel_EObject) (c2 : TTMetamodel_EObject) : bool :=
  match c1, c2 with
  | Build_TTMetamodel_EObject LocatedElementEClass o1, Build_TTMetamodel_EObject LocatedElementEClass o2 => beq_LocatedElement o1 o2
  end.

(* Typeclass Instance *)
Instance TTMetamodel : Metamodel TTMetamodel_EObject TTMetamodel_ELink TTMetamodel_EClass TTMetamodel_EReference :=
  {
    denoteModelClass := TTMetamodel_getTypeByEClass;
    denoteModelReference := TTMetamodel_getTypeByEReference;
    toModelClass := TTMetamodel_toEClass;
    toModelReference := TTMetamodel_toEReference;
    toModelElement := TTMetamodel_toEObjectOfEClass;
    toModelLink := TTMetamodel_toELinkOfEReference;
    beq_ModelElement := beq_TTMetamodel_Object;

    (* Theorems *)
    eqModelClass_dec := TTMetamodel_eqEClass_dec;
    eqModelReference_dec := TTMetamodel_eqEReference_dec;
  }.



