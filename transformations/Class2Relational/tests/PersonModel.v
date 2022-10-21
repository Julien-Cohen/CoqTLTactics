Require Import List.
Require Import String.

Require Import core.Model.

Require Import transformations.Class2Relational.ClassMetamodel.

(* 
    Class id=0 name='Person'
      Attribute id=1 derived=false name='parent' type='Person'
      Attribute id=2 derived=true name='sibling' type='Person'
*)

Definition PersonModel : Model ClassMetamodel.Object ClassMetamodel.Link :=
  (Build_Model
     (* elements *)
     (     (ClassObject (Build_Class 0 "Person")) 
        :: (AttributeObject (Build_Attribute 1 false "parent")) 
        :: (AttributeObject (Build_Attribute 2 true "sibling")) 
        :: nil)

     (* links *)
     (     (ClassAttributeLink (Build_ClassAttributes (Build_Class 0 "Person") ((Build_Attribute 1 false "parent")::nil))) 
        :: (AttributeTypeLink (Build_AttributeType (Build_Attribute 1 false "parent") (Build_Class 0 "Person"))) 
        :: (ClassAttributeLink (Build_ClassAttributes (Build_Class 0 "Person") ((Build_Attribute 2 true "sibling")::nil))) 
        :: (AttributeTypeLink (Build_AttributeType (Build_Attribute 2 true "sibling") (Build_Class 0 "Person"))) 
        :: nil)
  ).
