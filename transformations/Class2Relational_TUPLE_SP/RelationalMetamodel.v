Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import PeanoNat.
Require Import EqNat.
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import Glue.

(* Base types *)

Record Table_t := { table_id : nat ; table_name : string }.

Scheme Equality for Table_t.

Record Column_t := { column_id : nat ; column_name : string } .

Scheme Equality for Column_t.


Notation TableColumns_t := (Glue Table_t (list Column_t)) .

Notation ColumnReference_t := (Glue Column_t Table_t).




(* Generic types (data types) *)

Inductive Element : Set :=
  | TableElement : Table_t -> Element
  | ColumnElement : Column_t -> Element.

Scheme Equality for Element.


Inductive Link : Set :=
  | TableColumnLink : TableColumns_t -> Link
  | ColumnReferenceLink : ColumnReference_t -> Link.

(* Meta-types (kinds) *)

Inductive ElementKind : Set :=
  Table_K | Column_K.

Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | Table_K => Table_t
  | Column_K => Column_t
  end.

Definition lift_EKind (c: ElementKind) : (getTypeByEKind c) -> Element.
  destruct c ; [ exact TableElement | exact ColumnElement].
Defined.


Inductive LinkKind : Set :=
  TableColumns_K | ColumnReference_K.

Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | TableColumns_K => TableColumns_t
  | ColumnReference_K => ColumnReference_t
  end.

Definition lift_LKind (c: LinkKind) : (getTypeByLKind c) -> Link.
  destruct c ; [ exact TableColumnLink | exact ColumnReferenceLink].
Defined.


(* Reflective functions *)

Lemma eqClass_dec : forall (c1:ElementKind) (c2:ElementKind), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Lemma eqReference_dec : forall (c1:LinkKind) (c2:LinkKind), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.




Definition ClassAttributeTypes (c: ElementKind): Set :=
  match c with
  | Table_K => (nat * string)
  | Column_K => (nat * string)
  end.


Definition ReferenceRoleTypes (c:LinkKind): Set :=
  match c with
  | TableColumns_K => (Table_t * list Column_t)
  | ColumnReference_K => (Column_t * Table_t)
  end.

Definition Build_ReferenceLink (t : LinkKind) : (ReferenceRoleTypes t) -> Link :=
  match t with
  | TableColumns_K => (fun '(t,c) => (TableColumnLink (glue t with  c)))
  | ColumnReference_K => (fun '(c,t) => (ColumnReferenceLink ( glue c with t )))
  end.

Definition get_E_data (t : ElementKind) (c : Element) : option (getTypeByEKind t). 
  destruct t ; destruct c ; simpl.
  exact (Some t).
  exact None.
  exact None.
  exact (Some c).
Defined. 

Theorem toRelationalMetamodel_Class_inv :
  forall (t : ElementKind) (c :Element) (c': getTypeByEKind t),
    get_E_data t c = Some c' ->
    c = (lift_EKind t c').
Proof.
  intros.
  destruct t ; destruct c ; simpl in * ; congruence.
Qed.

Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t).
  destruct t ; destruct c ; simpl .
  exact (Some g).
  exact None.
  exact None.
  exact (Some g). 
Defined.

(** Typeclass instances *)

Definition RelationalMM : Metamodel :=
  {|
    ElementType := Element;
    LinkType := Link;
    elements_eq_dec := Element_eq_dec ;
  |}.


  #[export]
  Instance RelationalElementDenotation : Denotation Element ElementKind :=
  {
    denoteDatatype := getTypeByEKind;
    unbox := get_E_data;
    constructor := lift_EKind;
  }.
  
    

  #[export]
  Instance RelationalLinkDenotation : Denotation Link LinkKind :=
  {
    denoteDatatype := getTypeByLKind;
    unbox := get_L_data;
    constructor := lift_LKind;
  }.
  

  #[export]
  Instance RelationalMetamodel : ModelingMetamodel RelationalMM :=
  { 
      elements := RelationalElementDenotation;
      links := RelationalLinkDenotation;
  }.

Definition RelationalModel := Model RelationalMM.


(* General functions (to be used in transformations) *)


Definition getId (r : Element) : nat :=
  match r with
  | TableElement c => table_id c
  | ColumnElement a => column_id a
  end.

Definition getName (r : Element) : string :=
  match r with
  | TableElement c => table_name c
  | ColumnElement a => column_name a
  end.


Fixpoint getTableColumnsOnLinks (t : Table_t) (l : list Link) : option (list Column_t) :=
  match l with
  | (TableColumnLink (glue tab with c)) :: l1 => if Table_t_beq tab t then Some c else getTableColumnsOnLinks t l1
  | _ :: l1 => getTableColumnsOnLinks t l1
  | nil => None
  end.

Definition getTableColumns (t : Table_t) (m : RelationalModel) : option (list Column_t) :=
getTableColumnsOnLinks t m.(modelLinks).

Fixpoint getColumnReferenceOnLinks (c : Column_t) (l : list Link) : option Table_t :=
  match l with
  | (ColumnReferenceLink (glue col with t)) :: l1 => if Column_t_beq col c then Some t else getColumnReferenceOnLinks c l1
  | _ :: l1 => getColumnReferenceOnLinks c l1
  | nil => None
  end.

Definition getColumnReference (c : Column_t) (m : RelationalModel) : option Table_t := getColumnReferenceOnLinks c m.(modelLinks).

Definition bottomRelationalMetamodel_Class (k: ElementKind) : denoteDatatype k :=
  match k with
  | Table_K => (Build_Table_t 0 "")
  | Column_K => (Build_Column_t 0 "")
  end.

Lemma rel_invert : 
  forall (k: ElementKind) (t1 t2: denoteDatatype k),
    constructor k t1 = constructor k t2 -> t1 = t2.
Proof.
  unfold constructor ; simpl.
  unfold lift_EKind ; intros ; destruct k ; simpl in * ; congruence.
Qed.

Lemma rel_elink_invert : 
  forall (k: LinkKind) (t1 t2: denoteDatatype k), 
    constructor k t1 = constructor k t2 -> t1 = t2.
Proof.
  unfold constructor ; simpl.
  intros. destruct k ; simpl in * ; congruence.
Qed.

