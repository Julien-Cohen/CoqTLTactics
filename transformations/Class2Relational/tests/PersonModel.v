Require Import List.
Require Import String.

Require Import core.Model.

Require Import transformations.Class2Relational.ClassMetamodel.

(* 
    Class id=0 name='Person'
      Attribute id=1 derived=false name='parent' type='Person'
      Attribute id=2 derived=true name='sibling' type='Person'
*)

Definition PersonModel : Model ClassMetamodel.MM :=
  (Build_Model ClassMetamodel.MM
     (* elements *)
     (     (ClassElement (Build_Class_t 0 "Person")) 
        :: (AttributeElement (Build_Attribute_t 1 false "parent")) 
        :: (AttributeElement (Build_Attribute_t 2 true "sibling")) 
        :: nil)

     (* links *)
     (     (Class_attributesLink (Build_Class_attributes_t (Build_Class_t 0 "Person") ((Build_Attribute_t 1 false "parent")::nil))) 
        :: (Attribute_typeLink (Build_Attribute_type_t (Build_Attribute_t 1 false "parent") (Build_Class_t 0 "Person"))) 
        :: (Class_attributesLink (Build_Class_attributes_t (Build_Class_t 0 "Person") ((Build_Attribute_t 2 true "sibling")::nil))) 
        :: (Attribute_typeLink (Build_Attribute_type_t (Build_Attribute_t 2 true "sibling") (Build_Class_t 0 "Person"))) 
        :: nil)
  ).
