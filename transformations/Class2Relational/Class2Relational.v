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

Definition Class2Relational' :=
  transformation [ 
    rule "Class2Table"
    from [Class_K]
    to [ 
      ELEM "tab" ::: Table_K  
        fun _ _ c => return   {| 
          Table_id := c.(Class_id) ; 
          Table_name := c.(Class_name) 
        |} 
        
      LINK ::: Table_columns_K
         fun thisModule _ m c t =>
            c_attributes <- getClass_attributesElements c m ;
            res <- resolveAll thisModule "col" Column_K (singletons c_attributes) ;
            do_glue t with res 
         
    ] ; 

    rule "Attribute2Column"
    from [Attribute_K]
    where (fun _ a => negb a.(Attribute_derived))
    to [ 
      ELEM "col" ::: Column_K 
        fun _ _ a => return {| 
          Column_id := a.(Attribute_id) ;
          Column_name := a.(Attribute_name)
        |}
              
      LINK ::: Column_reference_K
         fun thisModule _ m a c =>
          a_type <- getAttribute_typeElement a m ;
          res <- resolve thisModule "tab" Table_K (singleton a_type) ;
          do_glue c with res           
         
    ]
  ].

Definition Class2Relational := parse Class2Relational'.

Close Scope coqtl.
