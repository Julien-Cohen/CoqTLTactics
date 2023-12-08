Require Import List.
Require Import String.

Require Import core.Model.

Require Import transformations.Class2Relational.ClassMetamodel.

Import Glue.

(* 
    Class id=0 name='Person'
      Attribute id=1 derived=false name='parent' type='Person'
      Attribute id=2 derived=true name='sibling' type='Person'
*)

Definition PersonModel : Model ClassMetamodel.MM :=
  (Build_Model ClassMetamodel.MM
     (* elements *)
     (     (ClassElement (Build_Class_t 0 "Person")) 
        :: (AttributeElement {| 
                Attribute_id := 1 ; 
                Attribute_derived := false ;
                Attribute_name := "parent" 
              |}) 
        :: (AttributeElement (Build_Attribute_t 2 true "sibling")) 
        :: nil)

     (* links *)
     (     (Class_attributesLink {| 
                src := Build_Class_t 0 "Person" ;
                trg := (Build_Attribute_t 1 false "parent")::nil
              |} )
        :: (Attribute_typeLink {| 
                                  src := Build_Attribute_t 1 false "parent" ;
                                  trg := Build_Class_t 0 "Person" |}
        ) 
        :: (Class_attributesLink {| 
                src := (Build_Class_t 0 "Person") ;
                trg := ((Build_Attribute_t 2 true "sibling")::nil) 
              |} ) 
        :: (Attribute_typeLink {| 
                src := Build_Attribute_t 2 true "sibling" ;
                trg := Build_Class_t 0 "Person" |}) 
        :: nil)
  ).
