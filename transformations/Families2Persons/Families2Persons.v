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
  Build_TransformationConfiguration FamiliesMetamodel_Metamodel_Instance PersonsMetamodel_Metamodel_Instance.

#[export]
Instance Families2PersonsConfiguration : ModelingTransformationConfiguration F2PConfiguration :=
 Build_ModelingTransformationConfiguration F2PConfiguration FamiliesMetamodel_ModelingMetamodel_Instance PersonsMetamodel_ModelingMetamodel_Instance.


Open Scope coqtl.

Definition Member_isFemale (m: Member) (f: FamiliesModel): bool :=
  match Member_getFamilyMother m f with
  | Some f => true
  | None => 
    match Member_getFamilyDaughter m f with
    | Some f => true
    | None => false
    end
  end.

Definition Member_getFamilyName (m: Member) (f: FamiliesModel): string :=
  match Member_getFamilyFather m f with
  | Some f => Family_getLastName f
  | None => 
    match Member_getFamilyMother m f with
    | Some f => Family_getLastName f
    | None => 
      match Member_getFamilySon m f with
      | Some f => Family_getLastName f
      | None => 
        match Member_getFamilyDaughter m f with
        | Some f => Family_getLastName f
        | None => ""
        end
      end
    end 
  end.

  Definition Families2Persons' :=
    transformation
    [
      rule "Member2Male"
      from [MemberClass]
      where (fun m member => negb (Member_isFemale member m))
      to 
      [
        ELEM "t" ::: MaleClass 
          << fun i m member => 
            return BuildMale (BuildPerson 
              ((Member_getFirstName member) ++ " " ++
                (Member_getFamilyName member m))) >>
          
      ];

      rule "Member2Female"
      from [MemberClass]
      where (fun m member => Member_isFemale member m)
      to 
      [
        ELEM "t" ::: FemaleClass 
          << fun i m member => 
            return BuildFemale (BuildPerson 
              ((Member_getFirstName member) ++ " " ++
                (Member_getFamilyName member m))) >>
          
      ]
    ].

Definition Families2Persons := parse Families2Persons'.

Close Scope coqtl.
