Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.

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
  Build_TransformationConfiguration ClassMM RelationalMM.

#[export] 
Instance Class2RelationalConfiguration : ModelingTransformationConfiguration C2RConfiguration :=
  Build_ModelingTransformationConfiguration C2RConfiguration ClassMetamodel RelationalMetamodel.

Open Scope coqtl.

Definition Class2Relational' :=
  transformation
  [
    rule "Class2Table"
    from [Class_K]

    to [ ELEM "tab" ::: Table_K  
        << fun _ _ c => Build_Table_t c.(class_id) c.(class_name) >>
        <<< LINK TableColumns_K //
               fun tls _ m c t =>
                  maybeBuildTableColumns t
                    (maybeResolveAll tls m "col" Column_K 
                       (maybeSingletons (getClassAttributesElements c m)))
        >>> ]
    ;
    rule "Attribute2Column"
    from [Attribute_K]
    where (fun _ a => negb a.(derived))
    to [ ELEM "col" ::: Column_K 
        << fun _ _ a => Build_Column_t a.(attr_id) a.(attr_name) >>
        <<< LINK ColumnReference_K //
               fun tls _ m a c =>
                  maybeBuildColumnReference c
                    (maybeResolve tls m "tab" Table_K 
                       (maybeSingleton (getAttributeTypeElement a m)))
        >>> ]
  ].

Definition Class2Relational := parse Class2Relational'.

Close Scope coqtl.
