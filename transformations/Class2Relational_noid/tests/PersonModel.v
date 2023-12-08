Require Import List.
Require Import String.

Require Import core.Model.

Require Import transformations.Class2Relational_noid.ClassMetamodel.

Import Glue.

(* 
    Class id=0 name='Person'
      Attribute id=1 derived=false name='parent' type='Person'
      Attribute id=2 derived=true name='sibling' type='Person'
*)

Definition PersonModel : Model ClassMetamodel.MM :=
  (Build_Model ClassMetamodel.MM
     (* elements *)
     (     (ClassElement (Build_Class_t "Person")) 
        :: (AttributeElement {| 
                
                Attribute_derived := false ;
                Attribute_name := "parent" 
              |}) 
        :: (AttributeElement (Build_Attribute_t true "sibling")) 
        :: nil)

     (* links *)
     (     (Class_attributesLink {| 
                src := Build_Class_t "Person" ;
                trg := (Build_Attribute_t false "parent")::nil
              |} )
        :: (Attribute_typeLink {| 
                                  src := Build_Attribute_t false "parent" ;
                                  trg := Build_Class_t "Person" |}
        ) 
        :: (Class_attributesLink {| 
                src := (Build_Class_t "Person") ;
                trg := ((Build_Attribute_t true "sibling")::nil) 
              |} ) 
        :: (Attribute_typeLink {| 
                src := Build_Attribute_t true "sibling" ;
                trg := Build_Class_t "Person" |}) 
        :: nil)
  ).
