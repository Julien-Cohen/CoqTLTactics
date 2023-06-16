(** Imports Native *)
Require Import String.
Require Import Bool.
Require Import List.
Require Import PeanoNat.
Require Import EqNat.

(** Imports CoqTL *)
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require        core.Tactics.

(** Base types for elements *)
Record Table_t := { Table_id : nat ; Table_name : string }.
Scheme Equality for Table_t.
Lemma lem_Table_t_beq_id: forall (e1 e2: Table_t), Table_t_beq e1 e2 = true -> e1 = e2.
Proof. exact internal_Table_t_dec_bl. Qed.
Lemma lem_Table_t_beq_refl: forall (e: Table_t), Table_t_beq e e = true.
Proof. intro ; apply internal_Table_t_dec_lb ; auto. Qed.


Record Column_t := { Column_id : nat ; Column_name : string }.
Scheme Equality for Column_t.
Lemma lem_Column_t_beq_id: forall (e1 e2: Column_t), Column_t_beq e1 e2 = true -> e1 = e2.
Proof. Tactics.beq_eq_tac. Qed.
Lemma lem_Column_t_beq_refl : forall (e: Column_t), Column_t_beq e e = true.
Proof. intro ; apply internal_Column_t_dec_lb ; auto. Qed. 

Global Hint Resolve lem_Column_t_beq_id : beq_eq_database.
(* (needed for the two lemmas below) *)


(** Base types for links *)
Record Table_columns_t := { Table_columns_t_source : Table_t ; Table_columns_t_target : list Column_t }.
Definition Table_columns_t_beq (a1 a2: Table_columns_t) : bool := 
  Table_t_beq a1.(Table_columns_t_source) a2.(Table_columns_t_source) && list_beq Column_t_beq a1.(Table_columns_t_target) a2.(Table_columns_t_target).
Lemma lem_Table_columns_t_beq_id : forall (e1 e2 : Table_columns_t), Table_columns_t_beq e1 e2 = true -> e1 = e2.
Proof. Tactics.beq_eq_tac. Qed.
Lemma lem_Table_columns_t_beq_refl : forall (e : Table_columns_t), Table_columns_t_beq e e = true.
Proof. destruct e. unfold Table_columns_t_beq. rewrite lem_Table_t_beq_refl. rewrite list_beq_refl. reflexivity. exact lem_Column_t_beq_refl. Qed. 


Record Column_reference_t := { Column_reference_t_source : Column_t ; Column_reference_t_target : Table_t }.
Scheme Equality for Column_reference_t.
Lemma lem_Column_reference_t_beq_id : forall (e1 e2 : Column_reference_t), Column_reference_t_beq e1 e2 = true -> e1 = e2.
Proof. Tactics.beq_eq_tac. Qed.



(** Data types for element (to build models) *)
Inductive Element : Set :=
  | TableElement : Table_t -> Element
  | ColumnElement : Column_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | Table_columnsLink : Table_columns_t -> Link
  | Column_referenceLink : Column_reference_t -> Link
.
(*Scheme Equality for Link. ==Does not work== *)

Definition Link_beq (c1 : Link) (c2 : Link) : bool :=
  match c1, c2 with
  | Table_columnsLink o1, Table_columnsLink o2 => Table_columns_t_beq o1 o2
  | Column_referenceLink o1, Column_referenceLink o2 => Column_reference_t_beq o1 o2
  | _, _ => false
  end.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | Table_K
  | Column_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | Table_columns_K
  | Column_reference_K
.
Scheme Equality for LinkKind.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)
Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | Table_K => Table_t
  | Column_K => Column_t
  end.


Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with
  | Table_K => TableElement
  | Column_K => ColumnElement
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (Table_K, TableElement v)  => Some v
  | (Column_K, ColumnElement v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | Table_columns_K => Table_columns_t
  | Column_reference_K => Column_reference_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | Table_columns_K => Table_columnsLink
  | Column_reference_K => Column_referenceLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (Table_columns_K, Table_columnsLink v)  => Some v
  | (Column_reference_K, Column_referenceLink v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eqdec := Element_beq ;
  links_eqdec := Link_beq
|}.


#[export]
Instance RelationalElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind ;
  unbox := get_E_data ;
  constructor := lift_EKind ;
}.


#[export]
Instance RelationalLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind ;
  unbox := get_L_data ;
  constructor := lift_LKind ;
}.


#[export]
Instance MMM : ModelingMetamodel MM :=
{
  elements := RelationalElementDenotation ;
  links := RelationalLinkDenotation ;
}.


Definition RelationalModel := Model MM.

(** General functions (used in transformations) *)
Fixpoint getTable_columnsOnLinks (t : Table_t) (l : list Link) : option (list Column_t) :=
 match l with
  | (Table_columnsLink x) :: l1 =>
    if Table_t_beq x.(Table_columns_t_source) t
      then (Some x.(Table_columns_t_target))
      else getTable_columnsOnLinks t l1
  | _ :: l1 => getTable_columnsOnLinks t l1
  | nil => None
 end.


Definition getTable_columns (t : Table_t) (m : RelationalModel) : option (list Column_t) :=
  getTable_columnsOnLinks t m.(modelLinks).


Fixpoint getColumn_referenceOnLinks (c : Column_t) (l : list Link) : option (Table_t) :=
 match l with
  | (Column_referenceLink (Build_Column_reference_t col t)) :: l1 => 
    if Column_t_beq col c 
      then Some t 
      else getColumn_referenceOnLinks c l1
  | _ :: l1 => getColumn_referenceOnLinks c l1
  | nil => None
 end.


Definition getColumn_reference (c : Column_t) (m : RelationalModel) : option (Table_t) :=
  getColumn_referenceOnLinks c m.(modelLinks).



(** Useful lemmas *)

(* FIXME : not used *)
Lemma Relational_invert : 
  forall (k: ElementKind) (t1 t2: getTypeByEKind k),
    constructor k t1 = constructor k t2 -> t1 = t2.
Proof. intro k ; destruct k ; simpl; congruence.  Qed. 


Lemma Element_dec : 
  forall (a: Element),
(instanceof Table_K a) = true\/(instanceof Column_K a) = true
.
Proof. destruct a ; auto. Qed. 


Lemma TableElement_cast :
  forall x y,
    unbox Table_K x = return y -> TableElement y = x.
Proof. destruct x ; destruct y ; compute ; congruence. Qed. 


Lemma ColumnElement_cast :
  forall x y,
    unbox Column_K x = return y -> ColumnElement y = x.
Proof. destruct x ; destruct y ; compute ; congruence. Qed. 

(** Manual addition *)
Definition maybeBuildColumnReference (c: Column_t) (t: option Table_t) : option Column_reference_t :=
  option_map (Build_Column_reference_t c) t.

 Ltac inv_maybeBuildColumnReference H := 
    match type of H with 
    | maybeBuildColumnReference _ _ = Some _ =>
        unfold maybeBuildColumnReference in H ; 
        OptionUtils.monadInv H
    end.


Definition maybeBuildTableColumns (t: Table_t) (c: option (list Column_t)) : option Table_columns_t :=
  option_map (Build_Table_columns_t t) c.

Ltac inv_maybeBuildTableColumns H := 
    match type of H with 
    | maybeBuildTableColumns _ _ = Some _ =>
        unfold maybeBuildTableColumns in H ; 
        OptionUtils.monadInv H
    end.


Definition getId (r : Element) : nat :=
  match r with
  | TableElement c => Table_id c
  | ColumnElement a => Column_id a
  end.

Definition getName (r : Element) : string :=
  match r with
  | TableElement c => Table_name c
  | ColumnElement a => Column_name a
  end.
