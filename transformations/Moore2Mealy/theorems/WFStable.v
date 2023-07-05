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
