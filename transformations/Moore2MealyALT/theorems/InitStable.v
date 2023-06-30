Require Moore2MealyALT.Moore2Mealy.
Require Moore2MealyALT.theorems.Elements.
Require Moore2MealyALT.theorems.WFStable.

Section Foo.

Variable (m:Moore.M).
  
Hypothesis WF_U : MooreWF.unique_ids m.

Lemma initial_state_preserved_fw2 : 
      forall s,
        MooreSemantics.initialState m = Some s ->
        MealySemantics.initialState (Semantics.execute Moore2Mealy.Moore2Mealy m) = Some (Elements.convert s).
Proof.
  intros s INIT.
  unfold MooreSemantics.initialState in INIT.
  unfold MealySemantics.initialState.
  apply OptionListUtils.find_lift_some in INIT. destruct INIT as (v & G & IN & E).
  destruct v ; [ PropUtils.inj G | discriminate G].  (* monadInv *)
  apply Id.internal_NodeId_dec_bl in E.
  destruct s.
  unfold Moore.State_id in E.
  subst.
  apply MealyWF.in_find ; [ apply MealyWF.always_unique_ids | | reflexivity ].
  apply Elements.state_element_fw.  exact IN.
Qed.

Lemma initial_state_preserved_fw3 : 
  MooreSemantics.initialState m = None ->
  MealySemantics.initialState (Semantics.execute Moore2Mealy.Moore2Mealy m) = None.
Proof.
  unfold MooreSemantics.initialState, MealySemantics.initialState.
  intros INIT.
  apply OptionListUtils.find_none.
  intros x H.

  destruct x ; [ right | left ; reflexivity].
  unfold Mealy.get_E_data.
  exists s ; split ; [ reflexivity | ].
  eapply Elements.state_element_bw in H.
  destruct H as (? & ? & ?). 
  subst.
  eapply OptionListUtils.find_none in INIT ; [ | exact H].

  unfold Moore.get_E_data in INIT.
  destruct INIT ; [ discriminate | ].
  destruct H0 as (? & ? & ?). PropUtils.inj H0.
  destruct x0 ; unfold Elements.convert, Mealy.State_id.
  unfold Moore.State_id in *.
  exact H1.
Qed.

Lemma initial_state_preserved : 
  MealySemantics.initialState (Semantics.execute Moore2Mealy.Moore2Mealy m) = option_map Elements.convert (MooreSemantics.initialState m).
Proof.
  destruct (MooreSemantics.initialState m) eqn:I ; unfold option_map.
  apply initial_state_preserved_fw2 ; assumption.
  apply initial_state_preserved_fw3 ; assumption.
  (* fixme : remove the two intermediate lemmas *)
Qed.

End Foo.
