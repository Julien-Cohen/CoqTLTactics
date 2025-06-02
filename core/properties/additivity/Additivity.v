From core.properties.additivity 
  Require Import RuleIncl Additivity_link.


Import TransformationConfiguration Syntax Semantics Model.

Definition Rule_Additivity {tc: TransformationConfiguration} :=
  forall (t1 t2: Transformation) (sm: SourceModel),
      RuleIncl.Transformation_incl_rules t1 t2 -> 
          Model_incl (execute t1 sm) (execute t2 sm). 

Theorem coqtl_not_additive : 
  exists (tc: TransformationConfiguration), 
  ~ (Rule_Additivity (tc:=tc)).
Proof.
  specialize (not_additivity_link) ; intro H.
  exists (Build_TransformationConfiguration Moore.MM Mealy.MM).


  contradict H.

  unfold Rule_Additivity_Link.
  unfold Rule_Additivity in H.
  intros.
  specialize (H t1 t2 sm H0).
  unfold Model_incl in H.
  destruct H as (_ & H).
   exact H.
Qed.
