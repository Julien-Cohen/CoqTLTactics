Require Import String.
Require Import List.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import Class2Relational.ClassMetamodel.
Require Import Class2Relational.RelationalMetamodel.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Import Glue.

(* module Class2Relational; 
   create OUT : RelationalMetamodel from IN : ClassMetamodel;

   rule Class2Table {
       from 
         c : Class
       to 
         tab: Table (
           id <- c.id,
           name <- c.name,
           columns <- c.attributes->collect(a | thisModule.resolve(a, 'col'))
         )
    }
    rule Attribute2Column {
        from 
          a : Attribute (not a.derived)
        to 
          col: Column (
            id <- a.id,
            name <- a.name,
            reference <- thisModule.resolve(a.type, 'tab')
          )
    }
   } *)

#[export]   
Instance C2RConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration ClassMetamodel.MM RelationalMetamodel.MM.

#[export] 
Instance Class2RelationalConfiguration : ModelingTransformationConfiguration C2RConfiguration :=
  Build_ModelingTransformationConfiguration C2RConfiguration ClassMetamodel.MMM RelationalMetamodel.MMM.

Open Scope coqtl.




Definition R1 : ConcreteRule := 
  rule "Class2Table"
    from [ (* c *) Class_K]

    to [ ELEM "tab" (* t *) ::: Table_K  
        << fun _ _ c => 
          {| 
            Table_id := c.(Class_id) ; 
            Table_name := c.(Class_name) 
          |}
            >>
        
        LINK ::: Table_columns_K
         << fun thisModule _ m c t =>
           try c_attributes := getClass_attributesElements c m
           in
           try res := resolveAll thisModule "col" Column_K (singletons c_attributes)
           in glue t with res 
            >> ].

(*rule Class2Table {
       from 
         c : Class
       to 
         tab: Table (
           id <- c.id,
           name <- c.name,
           columns <- c.attributes->collect(a | thisModule.resolve(a, 'col'))
         )
    }*)


Definition R2 : ConcreteRule :=
  rule "Attribute2Column"
    from [Attribute_K (* a *)]
    where (fun _ a => negb a.(Attribute_derived))
    to [ 
      ELEM "col" (* c *) ::: Column_K 
        << fun _ _ a =>
          {|
            Column_id := a.(Attribute_id) ;
            Column_name := a.(Attribute_name)
          |} >>
             
       LINK ::: Column_reference_K
       <<  fun thisModule _ m a c =>
         try a_type := getAttribute_typeElement a m 
          in
          try res := resolve thisModule "tab" Table_K (singleton a_type)
           in glue c with res 
                  
           >> 
    ].

(*rule Attribute2Column {
        from 
          a : Attribute (not a.derived)
        to 
          col: Column (
            id <- a.id,
            name <- a.name,
            reference <- thisModule.resolve(a.type, 'tab')
          )
    }
   }*)

Definition Class2Relational' :=
  transformation  [ R1 ; R2 ].

Definition Class2Relational := parse Class2Relational'.

Close Scope coqtl.
