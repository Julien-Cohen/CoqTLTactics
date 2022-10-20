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

(* Base types *)

Inductive
  Table : Set :=
  BuildTable :
    nat ->
    string -> Table.

Inductive
  Column : Set :=
  BuildColumn :
    nat ->
    string -> Column.

Inductive  
  TableColumns : Set :=
  BuildTableColumns :  Table -> list Column -> TableColumns.

Inductive  
  ColumnReference : Set :=
  BuildColumnReference : Column -> Table -> ColumnReference.

Definition maybeBuildColumnReference (c: Column) (t: option Table) : option ColumnReference :=
  match c, t with
  | c', Some t' => Some (BuildColumnReference c' t')
  | _, _ => None
  end.  

Definition maybeBuildTableColumns (t: Table) (c: option (list Column)) : option TableColumns :=
  match t, c with
  | t', Some c' => Some (BuildTableColumns t' c')
  | _, _ => None
  end.  

(* Accessors *)

Definition getTableId (t : Table) : nat :=
  match t with BuildTable id _ => id end.

Definition getTableName (t : Table) : string :=
  match t with BuildTable _ n => n end.

Definition getColumnId (c : Column) : nat :=
  match c with BuildColumn id _ => id end.

Definition getColumnName (c : Column) : string :=
  match c with BuildColumn _ n => n end.
  
Definition beq_Table (t1 : Table) (t2: Table) : bool :=
  beq_nat (getTableId t1) (getTableId t2) && beq_string (getTableName t1) (getTableName t2).

Definition beq_Column (c1 : Column) (c2 : Column) : bool :=
  beq_nat (getColumnId c1) (getColumnId c2) && beq_string (getColumnName c1) (getColumnName c2).

Lemma lem_beq_Table_id:
 forall (a1 a2: Table),
   beq_Table a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Table in H.
unfold "&&" in H.
destruct (getTableId a1 =? getTableId a2) eqn: ca1.
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
assert (true = PeanoNat.Nat.eqb n n). { apply beq_nat_refl. }
rewrite <- H.
assert (beq_string s s = true). { apply lem_beq_string_id. }
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
assert (beq_nat n n = true). {symmetry. apply beq_nat_refl. }
assert (beq_string s s = true). {apply lem_beq_string_id. }
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
destruct (getColumnId a1 =? getColumnId a2) eqn: ca1.
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
| BuildObject : forall (c:Classes), (getTypeByClass c) -> Object.

Definition beq_Object (c1 : Object) (c2 : Object) : bool :=
  match c1, c2 with
  | BuildObject TableClass o1, BuildObject TableClass o2 => beq_Table o1 o2
  | BuildObject ColumnClass o1, BuildObject ColumnClass o2 => beq_Column o1 o2
  | _, _ => false
  end.

Inductive Link : Set :=
| BuildLink : forall (c:References), (getTypeByReference c) -> Link.



(* Reflective functions *)

Lemma eqClass_dec : forall (c1:Classes) (c2:Classes), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Lemma eqReference_dec : forall (c1:References) (c2:References), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Definition getClass (c : Object) : Classes :=
  match c with
  | (BuildObject t _) => t
  end.

Definition getReference (c : Link) : References :=
  match c with
  | (BuildLink t _) => t
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
  | TableClass => (fun (p: nat * string) => (BuildObject TableClass (BuildTable (fst p) (snd p))))
  | ColumnClass => (fun (p: nat * string) => (BuildObject ColumnClass (BuildColumn (fst p) (snd p))))
  end.

Definition ReferenceRoleTypes (c:References): Set :=
  match c with
  | TableColumnsReference => (Table * list Column)
  | ColumnReferenceReference => (Column * Table)
  end.

Definition Build_ReferenceLink (t : References) : (ReferenceRoleTypes t) -> Link :=
  match t with
  | TableColumnsReference => (fun (p: Table * list Column) => (BuildLink TableColumnsReference (BuildTableColumns (fst p) (snd p))))
  | ColumnReferenceReference => (fun (p: Column * Table) => (BuildLink ColumnReferenceReference (BuildColumnReference (fst p) (snd p))))
  end.

Definition toRelationalMetamodel_Class (t : Classes) (c : Object) : option (getTypeByClass t) :=
  match c with
| BuildObject c0 d =>
    let s := eqClass_dec c0 t in
    match s with
    | left e => match e with
                     eq_refl => Some d
               end
    | right _ => None
    end
  end.

(*Proof.
  destruct c.
  destruct (RelationalMetamodel_eqClass_dec t r).
  - rewrite <- e in d.
    exact (Some d).
  - exact None.
Defined.*)

Theorem toRelationalMetamodel_Class_inv :
  forall (t : Classes) (c :Object) (c': getTypeByClass t),
    toRelationalMetamodel_Class t c = Some c' ->
    c = (BuildObject t c').
Proof.
  intros.
  destruct c.
  simpl in H.
  destruct (eqClass_dec c t).
  - destruct e. inversion H. reflexivity.
  - inversion H.
Qed.

Definition toRelationalMetamodel_Reference (t : References) (c : Link) : option (getTypeByReference t).
Proof.
  destruct c.
  destruct (eqReference_dec t c).
  - rewrite <- e in g.
    exact (Some g).
  - exact None.
Defined.

(* Generic functions *)

Definition toObjectFromTable (t :Table) : Object :=
  (BuildObject TableClass t).

Definition RelationalMetamodel_toObjectFromColumn (c :Column) : Object :=
  (BuildObject ColumnClass c).

Definition toObject (t: Classes) (e: getTypeByClass t) : Object:=
  (BuildObject t e).

Definition toLink (t: References) (e: getTypeByReference t) : Link :=
  (BuildLink t e).

Definition getId (r : Object) : nat :=
  match r with
  | (BuildObject TableClass c) => getTableId c
  | (BuildObject ColumnClass a) => getColumnId a
  end.

Definition getName (r : Object) : string :=
  match r with
  | (BuildObject TableClass c) => getTableName c
  | (BuildObject ColumnClass a) => getColumnName a
  end.

(*Definition allTables (m : RelationalModel) : list Table :=
  match m with BuildRelationalModel l _  => optionList2List (map (toRelationalMetamodel_Class TableClass) l) end.

Definition allColumns (m : RelationalModel) : list Column :=
  match m with BuildRelationalModel l _  => optionList2List (map (toRelationalMetamodel_Class ColumnClass) l) end.*)

Fixpoint getTableColumnsOnLinks (t : Table) (l : list Link) : option (list Column) :=
  match l with
  | (BuildLink TableColumnsReference (BuildTableColumns tab c)) :: l1 => if beq_Table tab t then Some c else getTableColumnsOnLinks t l1
  | _ :: l1 => getTableColumnsOnLinks t l1
  | nil => None
  end.

Definition getTableColumns (t : Table) (m : Model Object Link) : option (list Column) :=
getTableColumnsOnLinks t (allModelLinks m).

Fixpoint getColumnReferenceOnLinks (c : Column) (l : list Link) : option Table :=
  match l with
  | (BuildLink ColumnReferenceReference (BuildColumnReference col t)) :: l1 => if beq_Column col c then Some t else getColumnReferenceOnLinks c l1
  | _ :: l1 => getColumnReferenceOnLinks c l1
  | nil => None
  end.

Definition getColumnReference (c : Column) (m : Model Object Link) : option Table := getColumnReferenceOnLinks c (allModelLinks m).

Definition bottomRelationalMetamodel_Class (c: Classes) : (getTypeByClass c) :=
  match c with
  | TableClass => (BuildTable 0 "")
  | ColumnClass => (BuildColumn 0 "")
  end.

Lemma rel_invert : 
  forall (t: Classes) (t1 t2: getTypeByClass t), BuildObject t t1 = BuildObject t t2 -> t1 = t2.
Proof.
intros.
inversion H.
apply inj_pair2_eq_dec in H1.
exact H1.
apply eqClass_dec.
Qed.

Lemma rel_elink_invert : 
  forall (t: References) (t1 t2: getTypeByReference t), BuildLink t t1 = BuildLink t t2 -> t1 = t2.
Proof.
intros.
inversion H.
apply inj_pair2_eq_dec in H1.
exact H1.
apply eqReference_dec.
Qed.

  #[export]
  Instance RelationalElementSum : Sum Object Classes :=
  {
    denoteSubType := getTypeByClass;
    toSubType := toRelationalMetamodel_Class;
    toSumType := toObject;
  }.
  
  (* TODO *)
  Definition beq_Link (c1 : Link) (c2 : Link) : bool := true.
  
  #[export]
  Instance EqDec : EqDec Object := {
    eq_b := beq_Object;
  }.

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
  }.

  #[export]
  Instance RelationalMetamodel : ModelingMetamodel RelationalM :=
  { 
      elements := RelationalElementSum;
      links := RelationalLinkSum;
  }.

Definition RelationalModel := Model Object Link.

