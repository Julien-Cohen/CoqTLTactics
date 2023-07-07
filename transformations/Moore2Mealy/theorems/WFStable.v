Require Moore2Mealy.MooreSemantics.
Require Moore2Mealy.MealySemantics.
Require Moore2Mealy.Moore2Mealy.
Require Moore2Mealy.MooreWF.
Require Moore2Mealy.MealyWF.
Require Moore2Mealy.theorems.Elements.
Require Moore2Mealy.theorems.Links.

Import String.

Lemma unique_ids_preserved_fw : forall m,
    MooreWF.unique_ids m -> 
    MealyWF.unique_ids (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros ; apply MealyWF.always_unique_ids.
Qed.

Import Model Semantics.

Lemma WF_sourceLink_left_stable :
  forall m,
    Moore.WF_target m ->
    Moore.WF_source m -> 
    MooreWF.WF_sourceLink_left m -> 
    MealyWF.WF_sourceLink_left (Semantics.execute Moore2Mealy.Moore2Mealy m).
Proof.
  intros m WF1 WF2 WF4.
  unfold MealyWF.WF_sourceLink_left.
  intros. 

  destruct lk1 as (t' & s').
  destruct lk2 as (t'' & s'').
  simpl in H1. subst t''.
  f_equal.
  
  destruct (Links.source_link_bw _ WF1 WF2 _ _ H) as (s1 & C1 & IN1).
  destruct (Links.source_link_bw _ WF1 WF2 _ _ H0) as (s2 & C2 & IN2).

  specialize (WF4 _ _ IN1 IN2 (eq_refl _)). 
  PropUtils.inj WF4.
  reflexivity.
Qed.
