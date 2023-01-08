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

(** This transformation contains rule arity > 1 *)

(* module Class2Relational; 
   create OUT : RelationalMetamodel from IN : ClassMetamodel;

   rule Class2Table {
       from 
         c : Class
       to 
         tab: Table (
           id <- c.id,
           name <- c.name
         )
    }
    rule Attribute2Column {
        from 
          a : Attribute,
          c : Class
          (not a.derived and a.type = c)
        to 
          col: Column (
            id <- a.id,
            name <- a.name,
            reference <- thisModule.resolve(c, 'tab')
          )
    }
   } *)

#[export]
Instance C2RConfiguration : TransformationConfiguration := 
   Build_TransformationConfiguration ClassMM RelationalMM.

#[export]
Instance Class2RelationalConfiguration : ModelingTransformationConfiguration C2RConfiguration :=
   Build_ModelingTransformationConfiguration C2RConfiguration ClassMetamodel RelationalMetamodel.

Definition Class2Relational_arity :=
  buildTransformation 2
    [
      buildRule "Class2Table"
        (makeGuard [Class_K] (fun m c => true))
        (makeIterator [Class_K] (fun m c => 1))
        [buildOutputPatternElement "tab"
          (makeElement [Class_K] Table_K
            (fun i m c => Build_Table_t (class_id c) (class_name c)))
            (fun _ _ _ _ _ => return nil)
        ];
      buildRule "Attribute2Column"
        (makeGuard [Attribute_K; Class_K] 
          (fun m a cl => 
            andb (negb (derived a)) 
                 (is_option_eq (getAttributeType a m) cl beq_Class)))
        (makeIterator [Attribute_K; Class_K] (fun m a cl => 1))
        [buildOutputPatternElement "col"
          (makeElement [Attribute_K; Class_K] Column_K
            (fun i m a cl => Build_Column_t (attr_id a) (attr_name a)))
            (makeLink [Attribute_K; Class_K] Column_K ColumnReference_K
              (fun tls i m a cl c =>
                tb <- resolve tls m "tab" Table_K [ClassMetamodel.lift_EKind Class_K cl];
                return Build_ColumnReference_t c tb))
        ]
    ].
