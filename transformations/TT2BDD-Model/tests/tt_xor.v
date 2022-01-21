(********************************************************************
	@name Coq declarations for model
	@date 2020/12/16 10:49:27
	@description Automatically generated by XMI2Coq transformation.
 ********************************************************************)
		 
Require Import List.
Require Import core.Model.
Require Import String.
Require Import transformations.TT2BDD.TT.


Definition InputModel : Model TTMetamodel_EObject TTMetamodel_ELink :=
	(Build_Model
		(
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "769530879_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "482052083_InputPort" "" "b")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "1234250905_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port OutputPortEClass (BuildOutputPort "1720339_OutputPort" "" "s")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "38262958_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "1427040229_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1353530305_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "574268151_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "460201727_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1217875525_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "170144208_InputPort" "" "a")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "364639279_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1813187653_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "16868310_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1881901842_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "1787079037_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1604002113_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement TruthTableEClass (BuildTruthTable "837108062_TruthTable" "" "Test"))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "812586739_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "585324508_Cell" "" false))) :: 
		nil)
		(
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "769530879_Cell" "" false)  (BuildRow "1234250905_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "769530879_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "1234250905_Row" "")  (BuildTruthTable "837108062_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "1234250905_Row" "") ( (BuildCell "16868310_Cell" "" false) ::  (BuildCell "769530879_Cell" "" false) ::  (BuildCell "364639279_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "38262958_Cell" "" true)  (BuildRow "1427040229_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "38262958_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "1427040229_Row" "")  (BuildTruthTable "837108062_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "1427040229_Row" "") ( (BuildCell "1604002113_Cell" "" false) ::  (BuildCell "38262958_Cell" "" true) ::  (BuildCell "1217875525_Cell" "" true) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1353530305_Cell" "" true)  (BuildRow "1787079037_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1353530305_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "574268151_Cell" "" true)  (BuildRow "1787079037_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "574268151_Cell" "" true)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "1720339_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "460201727_Row" "")  (BuildTruthTable "837108062_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "460201727_Row" "") ( (BuildCell "812586739_Cell" "" true) ::  (BuildCell "1881901842_Cell" "" true) ::  (BuildCell "585324508_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1217875525_Cell" "" true)  (BuildRow "1427040229_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1217875525_Cell" "" true)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "1720339_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "364639279_Cell" "" false)  (BuildRow "1234250905_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "364639279_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "1720339_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1813187653_Cell" "" false)  (BuildRow "1787079037_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1813187653_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "170144208_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "16868310_Cell" "" false)  (BuildRow "1234250905_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "16868310_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "170144208_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1881901842_Cell" "" true)  (BuildRow "460201727_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1881901842_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "1787079037_Row" "")  (BuildTruthTable "837108062_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "1787079037_Row" "") ( (BuildCell "1813187653_Cell" "" false) ::  (BuildCell "1353530305_Cell" "" true) ::  (BuildCell "574268151_Cell" "" true) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1604002113_Cell" "" false)  (BuildRow "1427040229_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1604002113_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "170144208_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink TruthTablePortsEReference (BuildTruthTablePorts  (BuildTruthTable "837108062_TruthTable" "" "Test") ( (Build_Abstract_Port InputPortEClass  (BuildInputPort "170144208_Port" "" "a") ) ::  (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "b") ) ::  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "1720339_Port" "" "s") ) :: nil ))) ::
		(Build_TTMetamodel_ELink TruthTableRowsEReference (BuildTruthTableRows  (BuildTruthTable "837108062_TruthTable" "" "Test") ( (BuildRow "460201727_Row" "") ::  (BuildRow "1234250905_Row" "") ::  (BuildRow "1427040229_Row" "") ::  (BuildRow "1787079037_Row" "") :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "812586739_Cell" "" true)  (BuildRow "460201727_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "812586739_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "170144208_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "585324508_Cell" "" false)  (BuildRow "460201727_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "585324508_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "1720339_Port" "" "s") ))) ::
		nil)
	).
