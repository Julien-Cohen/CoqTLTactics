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

Definition Class2Relational :=
  buildTransformation 1
    [
      buildRule "Class2Table"
        (makeGuard [Class_K] (fun m c => true))
        (makeIterator [Class_K] (fun m c => 1))
        [buildOutputPatternElement "tab"
          (makeElement [Class_K] Table_K
            (fun i m c => Build_Table_t (class_id c) (class_name c)))
            (makeLink [Class_K] Table_K TableColumns_K
            (fun tls i m c t =>
              attrs <- getClassAttributes c m;
              cols <- resolveAll tls m "col" Column_K 
                (singletons (map (ClassMetamodel.lift_EKind Attribute_K) attrs));
              return Build_TableColumns_t t cols))
        ];
      buildRule "Attribute2Column"
        (makeGuard [Attribute_K] (fun m a => negb (derived a)))
        (makeIterator [Attribute_K] (fun m a => 1))
        [buildOutputPatternElement "col"
          (makeElement [Attribute_K] Column_K
            (fun i m a => Build_Column_t (attr_id a) (attr_name a)))
            (makeLink [Attribute_K] Column_K ColumnReference_K
              (fun tls i m a c =>
                cl <- getAttributeType a m;
                tb <- resolve tls m "tab" Table_K [ClassMetamodel.lift_EKind Class_K cl];
                return Build_ColumnReference_t c tb))
        ]
    ].
