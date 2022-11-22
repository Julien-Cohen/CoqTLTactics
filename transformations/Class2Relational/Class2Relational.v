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
  Build_TransformationConfiguration ClassM RelationalM.

#[export] 
Instance Class2RelationalConfiguration : ModelingTransformationConfiguration C2RConfiguration :=
  Build_ModelingTransformationConfiguration C2RConfiguration ClassMetamodel RelationalMetamodel.

Open Scope coqtl.

Definition Class2Relational' :=
  transformation
  [
    rule "Class2Table"
    from [Class_K]
    where (fun m a => true)
    to [elem [Class_K] TableClass "tab"
        (fun i m c => Build_Table (class_id c) (class_name c))
        [link [Class_K] TableClass TableColumnsReference
          (fun tls i m c t =>
            maybeBuildTableColumns t
              (maybeResolveAll tls m "col" ColumnClass 
                (maybeSingletons (getClassAttributesElements c m))))]]
    ;
    rule "Attribute2Column"
    from [Attribute_K]
    where (fun m a => negb (derived a))
    to [elem [Attribute_K] ColumnClass "col"
        (fun i m a => Build_Column (attr_id a) (attr_name a))
        [link [Attribute_K] ColumnClass ColumnReferenceReference
          (fun tls i m a c =>
            maybeBuildColumnReference c
              (maybeResolve tls m "tab" TableClass 
                (maybeSingleton (getAttributeTypeElement a m))))]]
  ].

Definition Class2Relational := parse Class2Relational'.

Close Scope coqtl.
