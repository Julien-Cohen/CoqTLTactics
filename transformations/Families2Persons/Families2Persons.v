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

Require Export Families2Persons.Families.
Require Export Families2Persons.Persons.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

#[export]
Instance F2PConfiguration : TransformationConfiguration := 
  Build_TransformationConfiguration Families.MM Persons.MM.

#[export]
Instance Families2PersonsConfiguration : ModelingTransformationConfiguration F2PConfiguration :=
 Build_ModelingTransformationConfiguration F2PConfiguration Families.MMM Persons.MMM. 


Open Scope coqtl.

Definition Member_isFemale (m:Member_t) (f:Families.M) (*fixme*): bool :=
  match getMember_familyMother f m with
  | Some f => true
  | None => 
    match getMember_familyDaughter f m with
    | Some f => true
    | None => false
    end
  end.

Definition Member_getFamilyName (m: Member_t) (f: Families.M): string :=
  match getMember_familyFather f m with
  | Some f => f.(Family_lastName)
  | None => 
    match getMember_familyMother f m with
    | Some f => f.(Family_lastName)
    | None => 
      match getMember_familySon f m with
      | Some f => f.(Family_lastName)
      | None => 
        match getMember_familyDaughter f m with
        | Some f => f.(Family_lastName)
        | None => ""
        end
      end
    end 
  end.

  Definition Families2Persons' :=
    transformation
    [
      rule "Member2Male"
      from [Member_K]
      where (fun m member => negb (Member_isFemale member m))
      to 
      [
        ELEM "t" ::: Male_K 
          << fun i m member => 
            return Build_Male_t (Build_Person_t 
              ((member.(Member_firstName)) ++ " " ++
                (Member_getFamilyName member m))) >>
          
      ];

      rule "Member2Female"
      from [Member_K]
      where (fun m member => Member_isFemale member m)
      to 
      [
        ELEM "t" ::: Female_K 
          << fun i m member => 
            return Build_Female_t (Build_Person_t 
              ((member.(Member_firstName)) ++ " " ++
                (Member_getFamilyName member m))) >>
          
      ]
    ].

Definition Families2Persons := parse Families2Persons'.

Close Scope coqtl.
