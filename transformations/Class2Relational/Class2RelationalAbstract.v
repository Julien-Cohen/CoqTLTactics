Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.

Require Import core.utils.Utils.

Require Import core.Syntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Require Import Class2Relational.ClassMetamodel.
Require Import Class2Relational.RelationalMetamodel.

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

Definition Class2Relational :=
  buildTransformation 1
    [
      buildRule "Class2Table"
        (makeGuard [Class_K] (fun m c => true))
        (makeIterator [Class_K] (fun m c => 1))
        [buildOutputPatternUnit "tab"
          (makeElement [Class_K] Table_K
            (fun i m c => return Build_Table_t (Class_id c) (Class_name c)))
            (Parser.dropToList(makeLink [Class_K] Table_K Table_columns_K
            (fun tls i m c t =>
              attrs <- getClass_attributes c m;
              cols <- resolveAll tls "col" Column_K 
                (singletons (map (ClassMetamodel.lift_EKind Attribute_K) attrs));
              do_glue t with cols)))
        ];
      buildRule "Attribute2Column"
        (makeGuard [Attribute_K] (fun m a => negb (Attribute_derived a)))
        (makeIterator [Attribute_K] (fun m a => 1))
        [buildOutputPatternUnit "col"
          (makeElement [Attribute_K] Column_K
            (fun i m a => return Build_Column_t (Attribute_id a) (Attribute_name a)))
            (Parser.dropToList(makeLink [Attribute_K] Column_K Column_reference_K
              (fun tls i m a c =>
                cl <- getAttribute_type a m;
                tb <- resolve tls "tab" Table_K [ClassMetamodel.lift_EKind Class_K cl];
                do_glue c with tb)))
        ]
    ].
