Require Import List.
Require Import String.

Require Import core.Model.

Require Import transformations.Class2Relational.ClassMetamodel.

(* 
    Class id=0 name='Person'
      Attribute id=1 derived=false name='parent' type='Person'
      Attribute id=2 derived=true name='sibling' type='Person'
*)

Definition PersonModel : Model ClassMetamodel_Object ClassMetamodel_Link :=
  (Build_Model
     (* elements *)
     (     (ClassMetamodel_BuildObject ClassClass (Build_Class 0 "Person")) 
        :: (ClassMetamodel_BuildObject AttributeClass (Build_Attribute 1 false "parent")) 
        :: (ClassMetamodel_BuildObject AttributeClass (Build_Attribute 2 true "sibling")) 
        :: nil)

     (* links *)
     (     (ClassMetamodel_BuildLink ClassAttributesReference (Build_ClassAttributes (Build_Class 0 "Person") ((Build_Attribute 1 false "parent")::nil))) 
        :: (ClassMetamodel_BuildLink AttributeTypeReference (Build_AttributeType (Build_Attribute 1 false "parent") (Build_Class 0 "Person"))) 
        :: (ClassMetamodel_BuildLink ClassAttributesReference (Build_ClassAttributes (Build_Class 0 "Person") ((Build_Attribute 2 true "sibling")::nil))) 
        :: (ClassMetamodel_BuildLink AttributeTypeReference (Build_AttributeType (Build_Attribute 2 true "sibling") (Build_Class 0 "Person"))) 
        :: nil)
  ).
