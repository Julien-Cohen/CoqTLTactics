Require Import String.
Require Import List.

Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.utils.Utils.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.
Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.tests.PersonModel.

(* Require Import Class2RelationalVerif. *)

(* Expected Output :
      = {|
       Model.modelElements := RelationalMetamodel.BuildEElement TableClass
                                (BuildTable 0 "Person")
                              :: RelationalMetamodel.BuildEElement ColumnClass
                                   (BuildColumn 1 "parent") :: nil;
       Model.modelLinks := RelationalMetamodel.BuildELink
                             TableColumnsReference
                             (BuildTableColumns (BuildTable 0 "Person")
                                (BuildColumn 1 "parent" :: nil))
                           :: RelationalMetamodel.BuildELink
                                ColumnReferenceReference
                                (BuildColumnReference
                                   (BuildColumn 1 "parent")
                                   (BuildTable 0 "Person")) :: nil |}
     : TargetModel RelationalMetamodel.EElement RelationalMetamodel.ELink
*)

(* Expected output (short):
    Table id=0 name='Person'
      Column id=1 name='parent' reference='Person'
*)

Compute 
  (Model_beq beq_Element beq_Link 
    (execute Class2Relational PersonModel) 
    {|
       Model.modelElements := RelationalMetamodel.TableElement
                                (Build_Table_t 0 "Person")
                              :: RelationalMetamodel.ColumnElement
                                   (Build_Column_t 1 "parent") :: nil;
       Model.modelLinks := RelationalMetamodel.TableColumnLink
                             (Build_TableColumns_t (Build_Table_t 0 "Person")
                                (Build_Column_t 1 "parent" :: nil))
                           :: RelationalMetamodel.ColumnReferenceLink
                                (Build_ColumnReference_t
                                   (Build_Column_t 1 "parent")
                                   (Build_Table_t 0 "Person")) :: nil |}).
(* Question : should we use [RelationalMetamodel.TableElement (Build_Table_t 0 "Person")] or [RelationalMetamodel.lift_EKind Table_K (Build_Table_t 0 "Person")] here ? *)
