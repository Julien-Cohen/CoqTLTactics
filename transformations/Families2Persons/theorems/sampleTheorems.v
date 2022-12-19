Require Import String.
Require Import List.

Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.Certification.
Require Import core.Syntax.
Require Import core.utils.Utils.
Require Import transformations.Families2Persons.Families2Persons.

Theorem tr_FamiliesToPersons :
    forall (sm : FamiliesModel) (te : PersonsMetamodel_Object), 
      In te (execute Families2Persons sm).(modelElements) ->
      (exists (se : FamiliesMetamodel_Object),
          In se sm.(modelElements) /\
          In te
            (instantiatePattern Families2Persons sm [se])).
Proof.
    intros.
    apply (tr_execute_in_elements Families2Persons) in H.
    destruct H.
    destruct H.
    destruct x.
    - contradiction H0.
    - destruct x.
      + exists s. 
        apply allTuples_incl in H.
        unfold incl in H.
        specialize (H s).
        crush.
      + exfalso. 
        specialize (allTuples_not_incl_length (s :: s0 :: x) Families2Persons sm).
        crush.
Qed.
