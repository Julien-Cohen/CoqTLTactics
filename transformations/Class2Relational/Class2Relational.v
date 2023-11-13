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

Notation "'try' x := e1 'in' e2" :=
  (match e1 with
   | None => None
   | Some x => e2 end)
    (right associativity, x name, at level 60).


(* Rule : 0 iterator, 0 guard, 1 link *)
(*
Notation "'rule' rulename 'from' ( x ::: type ) 'to' [ 'ELEM' k ::: t << op >> 'LINK' ::: k1 << oplink >> ]" :=

  (Build_ConcreteRule rulename [type] None None [ elem [type] t k op [link [type] t k1 oplink] ])
    (right associativity, at level 60):coqtl.
*)
(*Definition R1 : Class_t -> ConcreteRule := 
  rule "Class2Table"
    from ( self ::: Class_K )

    to [ ELEM "tab" ::: Table_K  
        << fun _ _ c => Build_Table_t c.(Class_id) c.(Class_name) >>
        LINK ::: Table_columns_K
        << fun tra _ m c t =>
                  maybeBuildTableColumns t
                    (maybeResolveAll tra "col" Column_K 
                       (maybeSingletons (getClass_attributesElements c m)))
                    >> ].
*)

(*Notation "'ITEXPR' source '->' 'collect' ( iterators | body ) 'END'" :=(source).*)


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
           option_map
            (Build_Table_columns_t t)
            (resolveAll thisModule "col" Column_K (singletons c_attributes))
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
         option_map 
           (Build_Column_reference_t c)
           (resolve thisModule "tab" Table_K (singleton a_type))
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
