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

Import Glue.

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

(* By removing beq on Links, we lose this.
Compute 
  (Model_beq   
    (execute Class2Relational PersonModel) 

    (Build_Model  
       RelationalMetamodel.MM 
       (RelationalMetamodel.TableElement
          (Build_Table_t 0 "Person")
          :: RelationalMetamodel.ColumnElement
          (Build_Column_t 1 "parent") :: nil)
       (RelationalMetamodel.Table_columnsLink
          (Build_Table_columns_t (Build_Table_t 0 "Person")
             (Build_Column_t 1 "parent" :: nil))
          :: RelationalMetamodel.Column_referenceLink
          (Build_Column_reference_t
             (Build_Column_t 1 "parent")
             (Build_Table_t 0 "Person")) :: nil))).
*)

Fact test_ok :    
    (execute Class2Relational PersonModel) 
      =
    (Build_Model  
       RelationalMetamodel.MM 
       (RelationalMetamodel.TableElement
          (Build_Table_t 0 "Person")
          
          :: RelationalMetamodel.ColumnElement
          (Build_Column_t 1 "parent") :: nil)
       
       (RelationalMetamodel.Table_columnsLink
          (glue (Build_Table_t 0 "Person")
             with (Build_Column_t 1 "parent" :: nil))
          
          :: RelationalMetamodel.Column_referenceLink
          (glue (Build_Column_t 1 "parent")
             with (Build_Table_t 0 "Person")) :: nil)).
Proof.
  reflexivity.
Qed.
