Require Import String.
Require Import List.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Require Import Glue.

Require Import Class2Relational_noid.ClassMetamodel.
Require Import Class2Relational_noid.RelationalMetamodel.



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
        fun _ _ cl => return   
          {| Table_name := cl.(Class_name) |} 
        
      LINK ::: Table_columns_K
        fun traces _ m cl tab =>
          attrs <- 
            getClass_attributesElements cl m ;
          cols <- resolveAll traces "col" Column_K 
            (singletons attrs) ;
          return {| src := tab; trg := cols |}
    ] ; 
        
    rule "Attribute2Column"
    from [Attribute_K]
      where (fun _ attr => negb attr.(Attribute_derived))
    to [ 
      ELEM "col" ::: Column_K 
        fun _ _ attr => return 
          {| Column_name := attr.(Attribute_name) |} 
              
      LINK ::: Column_reference_K
        fun traces _ m attr col =>
          typ <- getAttribute_typeElement attr m ;
          tab <- resolve traces "tab" Table_K 
            (singleton typ) ;
          return {| src := col; trg := tab |} 
    ] 
  ].

Definition Class2Relational := parse Class2Relational'.

Close Scope coqtl.
