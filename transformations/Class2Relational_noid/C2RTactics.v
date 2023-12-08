
Require Import core.utils.Utils.

Require Import core.Semantics.

Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational_noid.Class2Relational.
Require Import transformations.Class2Relational_noid.ClassMetamodel.
Require Import transformations.Class2Relational_noid.RelationalMetamodel.

From core Require TacticsFW Certification.


Ltac negb_inv H :=
  match type of H with
    negb (Attribute_derived _) = true => 
      apply Bool.negb_true_iff in H
  end.

Ltac unfold_toEData H :=
  unfold toEData in H ;
  simpl (unbox _) in H ;
  unfold get_E_data in H.


Ltac toEDataT H :=
   match type of H with
     toEData Table_K ?E = Some _ => 
       destruct E ; [ | discriminate H] 
   end.

Definition convert_class c :=
  {| 

    Table_name := c.(Class_name) 
  |}.

Definition convert_attribute c :=
  {| 

    Column_name := c.(Attribute_name)
  |}.

