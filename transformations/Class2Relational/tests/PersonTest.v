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
       Model.modelElements := RelationalMetamodel_BuildEObject TableClass
                                (BuildTable 0 "Person")
                              :: RelationalMetamodel_BuildEObject ColumnClass
                                   (BuildColumn 1 "parent") :: nil;
       Model.modelLinks := RelationalMetamodel_BuildELink
                             TableColumnsReference
                             (BuildTableColumns (BuildTable 0 "Person")
                                (BuildColumn 1 "parent" :: nil))
                           :: RelationalMetamodel_BuildELink
                                ColumnReferenceReference
                                (BuildColumnReference
                                   (BuildColumn 1 "parent")
                                   (BuildTable 0 "Person")) :: nil |}
     : TargetModel RelationalMetamodel_EObject RelationalMetamodel_ELink
*)

(* Expected output (short):
    Table id=0 name='Person'
      Column id=1 name='parent' reference='Person'
*)

Compute 
  (Model_beq beq_Object beq_Link 
    (execute Class2Relational PersonModel) 
    {|
       Model.modelElements := BuildObject TableClass
                                (BuildTable 0 "Person")
                              :: BuildObject ColumnClass
                                   (BuildColumn 1 "parent") :: nil;
       Model.modelLinks := BuildLink
                             TableColumnsReference
                             (BuildTableColumns (BuildTable 0 "Person")
                                (BuildColumn 1 "parent" :: nil))
                           :: BuildLink
                                ColumnReferenceReference
                                (BuildColumnReference
                                   (BuildColumn 1 "parent")
                                   (BuildTable 0 "Person")) :: nil |}).
