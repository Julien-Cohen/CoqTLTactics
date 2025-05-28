Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.

From Stdlib Require Import String.
From Stdlib Require Import EqNat.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import FunctionalExtensionality.


Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.


Require Import usertools.Glue.


Require Import Class2Relational.ClassMetamodel.
Require Import Class2Relational.RelationalMetamodel.



(*************************************************************)
(** * Universality of Stdlib.L (Model) on CR2 configuration     *)
(** * Using operational semantics                            *)
(*************************************************************)


#[export]   
Instance C2RConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration ClassMetamodel.MM RelationalMetamodel.MM.

#[export] 
Instance Class2RelationalConfiguration : ModelingTransformationConfiguration C2RConfiguration :=
  Build_ModelingTransformationConfiguration C2RConfiguration ClassMetamodel.MMM RelationalMetamodel.MMM.

Open Scope coqtl.

(* Only for reference *)
Definition Class2Relational_concrete   : ConcreteTransformation :=
  {| concreteRules := [ 

     
    {| 
      r_name := "Class2Table" ;
      r_InKinds := [Class_K] ;
      r_guard := None ;
      r_iter := None ;
      r_outpat := [ 
        elem 
          [Class_K]
          Table_K 
          "tab"%string    
          (fun _ _ c => return {| 
              Table_id := c.(Class_id) ; 
              Table_name := c.(Class_name) 
            |}
          ) 
        
          [ 
            link 
              [Class_K]
              Table_K 
              Table_columns_K
              (fun thisModule _ m c t =>
                c_attributes <- getClass_attributesElements c m ;
                res <- resolveAll thisModule "col" Column_K (singletons c_attributes) ;
                do_glue t with res
              ) 
          ]  
        ] 
    |} ; 

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
  ] |}.

(** Auxiliary functions *)

Definition get_table_i i (f: ClassModel -> RelationalModel) (m:ClassModel) :=  
  match nth_error ((f m).(modelElements)) i with 
            | Some (TableElement t) => Some t
            | Some _ => None
            | None => None
            end  .

Fixpoint getColumnReferenceLink (c : Column_t) (l : list Link) 
  : option Column_reference_glue :=
 match l with
  | (Column_referenceLink (glue col with t))  :: l1 => 
    if Column_t_beq col c 
      then Some (glue col with t)
      else getColumnReferenceLink c l1
  | _ :: l1 => getColumnReferenceLink c l1
  | nil => None
 end.

Fixpoint getTableColumnsLink (t : Table_t) (l : list Link) 
  : option Table_columns_glue :=
 match l with
  | (Table_columnsLink (glue t' with cols))  :: l1 => 
    if Table_t_beq t t' 
      then Some (glue t with cols)
      else getTableColumnsLink t l1
  | _ :: l1 => getTableColumnsLink t l1
  | nil => None
 end.


(* Universal transformation on C2R configuration *)
Definition universal_c2r_concrete (f: ClassModel -> RelationalModel) : ConcreteTransformation :=
  {| 
  concreteRules := [ 

    (* 2 rules *)
    {| 
      r_name := "buildTables" ;
      r_InKinds := nil ; (* only match the empty pattern *)
      r_guard := None ;
      r_iter := Some (fun sm => length (f sm).(modelElements)) ;
      r_outpat := [ 
        elem 
          nil (* kind of input pattern *)
          Table_K 
          "tab"%string    
          (fun i sm => get_table_i i f sm) 
        
          (* links *)
[ 
            (link 
              nil (* type de the input element *)
              Table_K (* type of the produced element *)
              Table_columns_K (* type of the produced link *)
        
          (fun thisModule _ m t => 
            let r := getTableColumnsLink t (f m).(modelLinks) 
            in r))

            

          ]  
        ] 
    |}  ;

    {| 
      r_name := "buildColumns" ;
      r_InKinds := nil ; (* only match the empty pattern *)
      r_guard := None ;
      r_iter := Some (fun sm => length (f sm).(modelElements)) ;
      r_outpat := [ 
        elem 
          nil (* kind of input pattern *)
          Column_K 
          "col"%string    
          (fun i sm => 
          match nth_error ((f sm).(modelElements)) i with 
            | Some (ColumnElement c) => Some c
            | Some _ => None
            | None => None
            end  
            
          ) 
        
          [ 
            (link 
              nil (* type of the input element *)
              Column_K (* type of the produced element *)
              Column_reference_K (* type of the produced link *)
        
          (fun thisModule _ m c => 
            let r := getColumnReferenceLink c (f m).(modelLinks) 
            in r))

            
          ]  
        ] 
    |}


  ] |}.

(* Tests *)

(* Expected result *)
Definition r : RelationalModel:= (Build_Model  
       RelationalMetamodel.MM 

        (* List of element (2 elements) *)
       (RelationalMetamodel.TableElement
          (Build_Table_t 0 "Person")
          
          :: RelationalMetamodel.ColumnElement
          (Build_Column_t 1 "parent") :: nil)
       

        (* List of links (2 links, the second one contains a list) *)
       (RelationalMetamodel.Table_columnsLink
          (glue (Build_Table_t 0 "Person")
             with (Build_Column_t 1 "parent" :: nil))
          
          :: RelationalMetamodel.Column_referenceLink
          (glue (Build_Column_t 1 "parent")
             with (Build_Table_t 0 "Person")) :: nil)).

(* Example of f function to reproduce *)
Definition test_f : ClassModel -> RelationalModel := 
  fun _ => r.

(* Universal transformation applied to f *)
Definition T := parse (universal_c2r_concrete test_f).

(* Example of input model *)
Require transformations.Class2Relational.tests.PersonModel.

(* Print the expected result then the obtained result *)
Eval cbv in r.
Eval cbv in (execute T PersonModel.PersonModel).

(* Check that the two are the same. *)
Fact test_ok : r = (execute T PersonModel.PersonModel).
Proof.
  reflexivity.
Qed.



