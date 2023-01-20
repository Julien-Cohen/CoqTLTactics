Require Import List.
Require Import String.

Require Import core.Model.

Require Import transformations.Class2Relational_TUPLE_SP.ClassMetamodel.

(* 
    Class id=0 name='Person'
      Attribute id=1 derived=false name='parent' type='Person'
      Attribute id=2 derived=true name='sibling' type='Person'
*)

Definition PersonModel : Model ClassMM :=
  (Build_Model ClassMM
     (* elements *)
     (     (ClassElement (Build_Class_t 0 "Person")) 
        :: (AttributeElement (Build_Attribute_t 1 false "parent")) 
        :: (AttributeElement (Build_Attribute_t 2 true "sibling")) 
        :: nil)

     (* links *)
     (     (ClassAttributeLink (Build_ClassAttributes_t (Build_Class_t 0 "Person") ((Build_Attribute_t 1 false "parent")::nil))) 
        :: (AttributeTypeLink (Build_AttributeType_t (Build_Attribute_t 1 false "parent") (Build_Class_t 0 "Person"))) 
        :: (ClassAttributeLink (Build_ClassAttributes_t (Build_Class_t 0 "Person") ((Build_Attribute_t 2 true "sibling")::nil))) 
        :: (AttributeTypeLink (Build_AttributeType_t (Build_Attribute_t 2 true "sibling") (Build_Class_t 0 "Person"))) 
        :: nil)
  ).
