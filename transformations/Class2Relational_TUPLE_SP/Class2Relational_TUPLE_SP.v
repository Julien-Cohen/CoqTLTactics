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

Require Import transformations.Class2Relational_TUPLE_SP.ClassMetamodel.
Require Import transformations.Class2Relational_TUPLE_SP.RelationalMetamodel.

(** This transformation contains rule arity > 1 *)

(* module Class2Relational; 
   create OUT : RelationalMetamodel from IN : ClassMetamodel;

   rule Class2Table {
       from 
         c : Class
       to 
         tab: Table (
           id <- c.id,
           name <- c.name,
           columns <- c.attributes->collect(a | thisModule.resolve([a, c], 'col'))
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

Open Scope coqtl.

Definition Class2Relational_TUPLE_SP' :=
  transformation
  [
    rule "Class2Table"
    from [Class_K]

    to [ ELEM "tab" ::: Table_K  
          << fun _ _ c => Build_Table_t c.(class_id) c.(class_name) >>
        
        LINK ::: TableColumns_K 
         << fun tls _ m c t =>
                  maybeBuildTableColumns t
                    (maybeResolveAll tls "col" Column_K 
                      (maybeTuples
                        (getClassAttributesElements c m) 
                        [(ClassElement c)]))
         >>
      ]
    ;
    rule "Attribute2Column"
    from [Attribute_K ; Class_K]
    where (fun m a cl => 
            andb (negb (derived a)) 
            (is_option_eq (getAttributeType a m) cl Class_t_beq))
    to [ ELEM "col" ::: Column_K 
         << fun _ _ a cl => Build_Column_t a.(attr_id) a.(attr_name) >>
        
        LINK ::: ColumnReference_K 
         << fun tls _ m a cl c =>
                  maybeBuildColumnReference c
                    (maybeResolve tls "tab" Table_K 
                       (maybeSingleton (Some (ClassElement cl))))
         >> ]
  ].

Definition Class2Relational_TUPLE_SP := parse Class2Relational_TUPLE_SP'.

Close Scope coqtl.
