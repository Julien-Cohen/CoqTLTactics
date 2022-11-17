Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import PeanoNat.
Require Import EqNat.
Require Import core.EqDec.
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import Coq.Logic.Eqdep_dec.

Scheme Equality for list.

(* Base types *)

Record Table := { table_id : nat ; table_name : string }.

Record Column := { column_id : nat ; column_name : string } .

Record TableColumns := { tab :  Table ; cols : list Column }.

Record ColumnReference := { cr : Column ; ct : Table }.

Definition maybeBuildColumnReference (c: Column) (t: option Table) : option ColumnReference :=
  match c, t with
  | c', Some t' => Some (Build_ColumnReference c' t')
  | _, _ => None
  end.  

Definition maybeBuildTableColumns (t: Table) (c: option (list Column)) : option TableColumns :=
  match t, c with
  | t', Some c' => Some (Build_TableColumns t' c')
  | _, _ => None
  end.  

(* Equality *)
  
Definition beq_Table (t1 : Table) (t2: Table) : bool :=
  beq_nat (table_id t1) (table_id t2) && beq_string (table_name t1) (table_name t2).

Definition beq_Column (c1 : Column) (c2 : Column) : bool :=
  beq_nat (column_id c1) (column_id c2) && beq_string (column_name c1) (column_name c2).

Definition beq_TableColumns (c1 : TableColumns) (c2 : TableColumns) : bool :=
  beq_Table (tab c1) (tab c2) && list_beq Column beq_Column (cols c1) (cols c2).

Definition beq_ColumnReference (c1 : ColumnReference) (c2 : ColumnReference) : bool :=
  beq_Column (cr c1) (cr c2) && beq_Table (ct c1) (ct c2).

Lemma lem_beq_Table_id:
 forall (a1 a2: Table),
   beq_Table a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Table in H.
unfold "&&" in H.
destruct (table_id a1 =? table_id a2) eqn: ca1.
- apply (lem_beq_string_eq2) in H.
  apply (beq_nat_true) in ca1.
  destruct a1,a2.
  simpl in ca1, H.
  rewrite ca1,H.
  auto.
- congruence.
Qed.

Lemma lem_beq_Table_refl:
 forall (a: Table),
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
 forall (c: Column),
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
 forall (a1 a2: Column),
   beq_Column a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Column in H.
unfold "&&" in H.
destruct (column_id a1 =? column_id a2) eqn: ca1.
- apply (lem_beq_string_eq2) in H.
  apply (beq_nat_true) in ca1.
  destruct a1,a2.
  simpl in ca1, H.
  rewrite ca1,H.
  auto.
- congruence.
Qed.

(* Meta-types *)

Inductive Classes : Set :=
  TableClass | ColumnClass.

Definition getTypeByClass (type : Classes) : Set :=
  match type with
  | TableClass => Table
  | ColumnClass => Column
  end.

Inductive References : Set :=
  TableColumnsReference | ColumnReferenceReference.

Definition getTypeByReference (type : References) : Set :=
  match type with
  | TableColumnsReference => TableColumns
  | ColumnReferenceReference => ColumnReference
  end.

(* Generic types *)

Inductive Object : Set :=
  | TableObject : Table -> Object
  | ColumnObject : Column -> Object.

Definition toObject (c: Classes) : (getTypeByClass c) -> Object.
  destruct c ; simpl ; intro a.
  exact (TableObject a).
  exact (ColumnObject a).
Defined.

Definition beq_Object (c1 : Object) (c2 : Object) : bool :=
  match c1, c2 with
  | TableObject o1, TableObject o2 => beq_Table o1 o2
  | ColumnObject o1, ColumnObject o2 => beq_Column o1 o2
  | _, _ => false
  end.

Inductive Link : Set :=
  | TableColumnLink : TableColumns -> Link
  | ColumnReferenceLink : ColumnReference -> Link.

(* Reflective functions *)

Lemma eqClass_dec : forall (c1:Classes) (c2:Classes), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Lemma eqReference_dec : forall (c1:References) (c2:References), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Definition getClass (c : Object) : Classes :=
  match c with
  | TableObject _ => TableClass
  | ColumnObject _ => ColumnClass
  end.

Definition getReference (c : Link) : References :=
  match c with
  | TableColumnLink _ => TableColumnsReference
  | ColumnReferenceLink _ => ColumnReferenceReference
  end.

Definition instanceOfClass (cmc: Classes) (c : Object): bool :=
  if eqClass_dec (getClass c) cmc then true else false.

Definition instanceOfReference (cmr: References) (c : Link): bool :=
  if eqReference_dec (getReference c) cmr then true else false.

Definition ClassAttributeTypes (c: Classes): Set :=
  match c with
  | TableClass => (nat * string)
  | ColumnClass => (nat * string)
  end.

Definition ClassElement (t : Classes) : (ClassAttributeTypes t) -> Object :=
  match t with
  | TableClass => (fun (p: nat * string) => (TableObject (Build_Table (fst p) (snd p))))
  | ColumnClass => (fun (p: nat * string) => (ColumnObject (Build_Column (fst p) (snd p))))
  end.

Definition ReferenceRoleTypes (c:References): Set :=
  match c with
  | TableColumnsReference => (Table * list Column)
  | ColumnReferenceReference => (Column * Table)
  end.

Definition Build_ReferenceLink (t : References) : (ReferenceRoleTypes t) -> Link :=
  match t with
  | TableColumnsReference => (fun (p: Table * list Column) => (TableColumnLink (Build_TableColumns (fst p) (snd p))))
  | ColumnReferenceReference => (fun (p: Column * Table) => (ColumnReferenceLink (Build_ColumnReference (fst p) (snd p))))
  end.

Definition toRelationalMetamodel_Class (t : Classes) (c : Object) : option (getTypeByClass t). 
  destruct t ; destruct c ; simpl.
  exact (Some t).
  exact None.
  exact None.
  exact (Some c).
Defined. 

Theorem toRelationalMetamodel_Class_inv :
  forall (t : Classes) (c :Object) (c': getTypeByClass t),
    toRelationalMetamodel_Class t c = Some c' ->
    c = (toObject t c').
Proof.
  intros.
  destruct t ; destruct c ; simpl in * ; congruence.
Qed.

Definition toRelationalMetamodel_Reference (t : References) (c : Link) : option (getTypeByReference t).
  destruct t ; destruct c ; simpl .
  exact (Some t).
  exact None.
  exact None.
  exact (Some c). 
Defined.

(* Generic functions *)

Definition toLink (t: References) (e: getTypeByReference t) : Link.
  destruct t ; simpl in *.
  exact (TableColumnLink e).
  exact (ColumnReferenceLink e).
  Defined.

Definition getId (r : Object) : nat :=
  match r with
  | TableObject c => table_id c
  | ColumnObject a => column_id a
  end.

Definition getName (r : Object) : string :=
  match r with
  | TableObject c => table_name c
  | ColumnObject a => column_name a
  end.

(*Definition allTables (m : RelationalModel) : list Table :=
  match m with BuildRelationalModel l _  => optionList2List (map (toRelationalMetamodel_Class TableClass) l) end.

Definition allColumns (m : RelationalModel) : list Column :=
  match m with BuildRelationalModel l _  => optionList2List (map (toRelationalMetamodel_Class ColumnClass) l) end.*)

Fixpoint getTableColumnsOnLinks (t : Table) (l : list Link) : option (list Column) :=
  match l with
  | (TableColumnLink (Build_TableColumns tab c)) :: l1 => if beq_Table tab t then Some c else getTableColumnsOnLinks t l1
  | _ :: l1 => getTableColumnsOnLinks t l1
  | nil => None
  end.

Definition getTableColumns (t : Table) (m : Model Object Link) : option (list Column) :=
getTableColumnsOnLinks t (allModelLinks m).

Fixpoint getColumnReferenceOnLinks (c : Column) (l : list Link) : option Table :=
  match l with
  | (ColumnReferenceLink (Build_ColumnReference col t)) :: l1 => if beq_Column col c then Some t else getColumnReferenceOnLinks c l1
  | _ :: l1 => getColumnReferenceOnLinks c l1
  | nil => None
  end.

Definition getColumnReference (c : Column) (m : Model Object Link) : option Table := getColumnReferenceOnLinks c (allModelLinks m).

Definition bottomRelationalMetamodel_Class (c: Classes) : (getTypeByClass c) :=
  match c with
  | TableClass => (Build_Table 0 "")
  | ColumnClass => (Build_Column 0 "")
  end.

Lemma rel_invert : 
  forall (t: Classes) (t1 t2: getTypeByClass t), toObject t t1 = toObject t t2 -> t1 = t2.
Proof.
  unfold toObject ; intros ; destruct t ; simpl in * ; congruence.
Qed.

Lemma rel_elink_invert : 
  forall (t: References) (t1 t2: getTypeByReference t), toLink t t1 = toLink t t2 -> t1 = t2.
Proof.
  intros. destruct t ; simpl in * ; congruence.
Qed.

  #[export]
  Instance RelationalElementSum : Sum Object Classes :=
  {
    denoteSubType := getTypeByClass;
    toSubType := toRelationalMetamodel_Class;
    toSumType := toObject;
  }.
  
  Definition beq_Link (c1 : Link) (c2 : Link) : bool :=
    match c1, c2 with
    | TableColumnLink o1, TableColumnLink o2 => beq_TableColumns o1 o2
    | ColumnReferenceLink o1, ColumnReferenceLink o2 => beq_ColumnReference o1 o2
    | _, _ => false
    end.
    

  #[export]
  Instance RelationalLinkSum : Sum Link References :=
  {
    denoteSubType := getTypeByReference;
    toSubType := toRelationalMetamodel_Reference;
    toSumType := toLink;
  }.
  
  #[export]
  Instance RelationalM : Metamodel :=
  {
    ModelElement := Object;
    ModelLink := Link;
    elements_eqdec:= beq_Object ;
  }.

  #[export]
  Instance RelationalMetamodel : ModelingMetamodel RelationalM :=
  { 
      elements := RelationalElementSum;
      links := RelationalLinkSum;
  }.

Definition RelationalModel := Model Object Link.

