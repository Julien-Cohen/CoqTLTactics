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
Require        core.Tactics.

Require Import Coq.Logic.Eqdep_dec.


(* Base types *)

Record Table_t := { table_id : nat ; table_name : string }.

Record Column_t := { column_id : nat ; column_name : string } .

Record TableColumns_t := { tab : Table_t ; cols : list Column_t }.

Record ColumnReference_t := { cr : Column_t ; ct : Table_t }.

Definition maybeBuildColumnReference (c: Column_t) (t: option Table_t) : option ColumnReference_t :=
  match t with
  | Some t' => Some (Build_ColumnReference_t c t')
  | _ => None
  end.  

Definition maybeBuildTableColumns (t: Table_t) (c: option (list Column_t)) : option TableColumns_t :=
  match c with
  | Some c' => Some (Build_TableColumns_t t c')
  | _ => None
  end.  

(* Equality *)
  
Definition beq_Table (t1 : Table_t) (t2: Table_t) : bool :=
  beq_nat (table_id t1) (table_id t2) && beq_string (table_name t1) (table_name t2).

Definition beq_Column (c1 : Column_t) (c2 : Column_t) : bool :=
  beq_nat (column_id c1) (column_id c2) && beq_string (column_name c1) (column_name c2).

Definition beq_TableColumns (c1 : TableColumns_t) (c2 : TableColumns_t) : bool :=
  beq_Table (tab c1) (tab c2) && list_beq beq_Column (cols c1) (cols c2).

Definition beq_ColumnReference (c1 : ColumnReference_t) (c2 : ColumnReference_t) : bool :=
  beq_Column (cr c1) (cr c2) && beq_Table (ct c1) (ct c2).


Lemma lem_beq_Table_id:
 forall (a1 a2: Table_t),
   beq_Table a1 a2 = true -> a1 = a2.
Proof.
  Tactics.beq_eq_tac.
Qed.

Lemma lem_beq_Table_refl:
 forall (a: Table_t),
   beq_Table a a = true.
Proof.
intros.
destruct a.
unfold beq_Table.
simpl.
assert (true = PeanoNat.Nat.eqb table_id0 table_id0). { apply beq_nat_refl. }
rewrite <- H.
assert (beq_string table_name0 table_name0 = true). { apply lem_beq_string_id. }
rewrite H0.
simpl.
auto.
Qed.

Lemma lem_beq_Column_refl : 
 forall (c: Column_t),
   beq_Column c c = true.
Proof.
intros.
destruct c.
unfold beq_Column.
simpl.
assert (beq_nat column_id0 column_id0 = true). {symmetry. apply beq_nat_refl. }
assert (beq_string column_name0 column_name0 = true). {apply lem_beq_string_id. }
rewrite H,H0.
simpl.
auto.
Qed.

Lemma lem_beq_Column_id:
 forall (a1 a2: Column_t),
   beq_Column a1 a2 = true -> a1 = a2.
Proof.
  Tactics.beq_eq_tac.
Qed.

Hint Resolve lem_beq_Column_id : beq_eq_database.
(* (needed for the two lemmas below) *)

Lemma lem_beq_TableColumns_id:
 forall a1 a2,
   beq_TableColumns a1 a2 = true -> a1 = a2.
Proof. 
  Tactics.beq_eq_tac.
Qed.

Lemma lem_beq_ColumnReference_id:
 forall a1 a2,
   beq_ColumnReference a1 a2 = true -> a1 = a2.
Proof. 
  Tactics.beq_eq_tac.
Qed.


(* Generic types (data types) *)

Inductive Element : Set :=
  | TableElement : Table_t -> Element
  | ColumnElement : Column_t -> Element.


Definition beq_Element (c1 : Element) (c2 : Element) : bool :=
  match c1, c2 with
  | TableElement o1, TableElement o2 => beq_Table o1 o2
  | ColumnElement o1, ColumnElement o2 => beq_Column o1 o2
  | _, _ => false
  end.

Inductive Link : Set :=
  | TableColumnLink : TableColumns_t -> Link
  | ColumnReferenceLink : ColumnReference_t -> Link.

  Definition beq_Link (c1 : Link) (c2 : Link) : bool :=
    match c1, c2 with
    | TableColumnLink o1, TableColumnLink o2 => beq_TableColumns o1 o2
    | ColumnReferenceLink o1, ColumnReferenceLink o2 => beq_ColumnReference o1 o2
    | _, _ => false
    end.

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
  | TableColumns_K => (fun (p: Table_t * list Column_t) => (TableColumnLink (Build_TableColumns_t (fst p) (snd p))))
  | ColumnReference_K => (fun (p: Column_t * Table_t) => (ColumnReferenceLink (Build_ColumnReference_t (fst p) (snd p))))
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
  exact (Some t).
  exact None.
  exact None.
  exact (Some c). 
Defined.

Definition RelationalMM : Metamodel :=
  {|
    ElementType := Element;
    LinkType := Link;
    elements_eqdec := beq_Element ;
    links_eqdec := beq_Link
  |}.



(* Generic functions *)


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
  | (TableColumnLink (Build_TableColumns_t tab c)) :: l1 => if beq_Table tab t then Some c else getTableColumnsOnLinks t l1
  | _ :: l1 => getTableColumnsOnLinks t l1
  | nil => None
  end.

Definition getTableColumns (t : Table_t) (m : Model RelationalMM) : option (list Column_t) :=
getTableColumnsOnLinks t m.(modelLinks).

Fixpoint getColumnReferenceOnLinks (c : Column_t) (l : list Link) : option Table_t :=
  match l with
  | (ColumnReferenceLink (Build_ColumnReference_t col t)) :: l1 => if beq_Column col c then Some t else getColumnReferenceOnLinks c l1
  | _ :: l1 => getColumnReferenceOnLinks c l1
  | nil => None
  end.

Definition getColumnReference (c : Column_t) (m : Model RelationalMM) : option Table_t := getColumnReferenceOnLinks c m.(modelLinks).

Definition bottomRelationalMetamodel_Class (c: ElementKind) : (getTypeByEKind c) :=
  match c with
  | Table_K => (Build_Table_t 0 "")
  | Column_K => (Build_Column_t 0 "")
  end.

Lemma rel_invert : 
  forall (t: ElementKind) (t1 t2: getTypeByEKind t), lift_EKind t t1 = lift_EKind t t2 -> t1 = t2.
Proof.
  unfold lift_EKind ; intros ; destruct t ; simpl in * ; congruence.
Qed.

Lemma rel_elink_invert : 
  forall (t: LinkKind) (t1 t2: getTypeByLKind t), lift_LKind t t1 = lift_LKind t t2 -> t1 = t2.
Proof.
  intros. destruct t ; simpl in * ; congruence.
Qed.

  #[export]
  Instance RelationalElementSum : Sum Element ElementKind :=
  {
    denoteDatatype := getTypeByEKind;
    unbox := get_E_data;
    constructor := lift_EKind;
  }.
  
    

  #[export]
  Instance RelationalLinkSum : Sum Link LinkKind :=
  {
    denoteDatatype := getTypeByLKind;
    unbox := get_L_data;
    constructor := lift_LKind;
  }.
  

  #[export]
  Instance RelationalMetamodel : ModelingMetamodel RelationalMM :=
  { 
      elements := RelationalElementSum;
      links := RelationalLinkSum;
  }.

Definition RelationalModel := Model RelationalMM.

