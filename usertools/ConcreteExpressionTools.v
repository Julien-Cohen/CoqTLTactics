(** Tools to deal with [ConcreteExpression] constructions. Concrete expressions are built from user defined rules at parsing by [makeElement], [makeGuard], [makeGuard]... *)

From core 
  Require Import ConcreteExpressions.

Import Utils.


(** * Auxiliary lemmas and tactics *)


Lemma drop_true a :
  drop_option_to_bool a = true -> a = Some true.
Proof.
  destruct a ; simpl ; intro.
  + congruence.
  + discriminate.
Qed.


Ltac exploit_toEData H :=
  match type of H with
  | ModelingMetamodel.toEData _ _ = Some ?V =>
      compute in H ; first [ inj H | discriminate H] ; try subst V
  | ModelingMetamodel.toEData _ ?e = Some ?V =>
      destruct e ; compute in H ; first [ inj H | discriminate H] ; try subst V
  end.


Ltac dummy_inv H :=
  match type of H with 
    | ConcreteExpressions.dummy _ true _ = true =>
        clear H
  end.


(** * On [wrap] *)
(** [wrap] is a pivot for [makeElement], [makeGuard], [makeGuard]... *)


Lemma wrap_inv_nil 
        {tc : TransformationConfiguration.TransformationConfiguration}
        {mtc: ModelingTransformationConfiguration.ModelingTransformationConfiguration tc}
T b c (e:T) : 
  wrap nil b c  = Some e ->
  b = e /\ c = nil.
Proof.
  destruct c ; simpl. 
  { intro H ; injection H ; intro ; subst ; split ; auto. }
  { intro ; discriminate. }
Qed.

Lemma wrap_inv_nil_nil 
  {tc : TransformationConfiguration.TransformationConfiguration}
  {mtc: ModelingTransformationConfiguration.ModelingTransformationConfiguration tc}
  T b (e:T) : 
  wrap nil b nil  = Some e ->
  b = e .
Proof.
  simpl. 
  intro H ; inj H ; auto. 
Qed.

Lemma wrap_inv_cons 
  {tc : TransformationConfiguration.TransformationConfiguration}
  {mtc: ModelingTransformationConfiguration.ModelingTransformationConfiguration tc}
  T a b c d (e:T) : 
  wrap (cons a b) c d  = Some e ->
  exists a' b' x,
    d = cons a' b' /\ ModelingMetamodel.toEData a a' = Some x /\ wrap b (c x) b' = return e.
Proof.
  destruct d ; simpl.
  { intro H ; discriminate H. }
  {
    destruct_match_G ; simpl.
    {

      intros.  
      eexists ; eexists ; eexists.
      repeat (split ; eauto).
    }
    { intro H ; discriminate H. }
  }
Qed.

Lemma wrap_inv_cons_cons
  {tc : TransformationConfiguration.TransformationConfiguration}
  {mtc: ModelingTransformationConfiguration.ModelingTransformationConfiguration tc}

  T a b c a' b' (e:T) : 
  wrap (cons a b) c (cons a' b') = Some e ->
  exists x, 
    ModelingMetamodel.toEData a a' = Some x /\ wrap b (c x) b' = return e.
Proof.
  simpl.
  destruct_match_G ; simpl.
  {
    intros.  
    eexists.
    repeat (split ; eauto).
  }
  { intro H ; discriminate H. }
Qed.


Ltac wrap_inv H :=
   match type of H with
   | ConcreteExpressions.wrap (cons _ _) _ (cons _ _) = Some  _ =>
       apply wrap_inv_cons_cons in H ;

       let e:= fresh "e" in 
       let T_e := fresh "T_e" in
       let TMP := fresh "TMP" in 
        (* Hypothesis that are introduced by Context are not erased by destruct.
           TMP is a bypass for this case. *)
        destruct H as (e & T_e & TMP) ; try clear H ; rename TMP into H ; 
        exploit_toEData T_e 

   | ConcreteExpressions.wrap (cons _ _) _ ?SP = Some  _ =>
       
       apply wrap_inv_cons in H ;
        let e := fresh "e" in
        let sp := fresh "sp" in 
        let t:= fresh "t" in 
        let E := fresh "E" in
        let T_e := fresh "T_e" in
        let TMP := fresh "TMP" in 
         destruct H as (e & sp & t & E & T_e & TMP) ; try clear H ; rename TMP into H ;
        exploit_toEData T_e ;
        try subst SP  

   | ConcreteExpressions.wrap nil _ nil = Some ?V =>
       apply wrap_inv_nil_nil in H ;
       try first [subst V | inj H | dummy_inv H ]
   | ConcreteExpressions.wrap nil _ ?SP = Some ?V =>
       apply wrap_inv_nil in H ;
        let E := fresh "E" in 
        destruct H as [H E] (* and *) ; 
       try subst SP ;
       try first [subst V | inj H | dummy_inv H ]
   end.


(** * On [makeElement], [makeGuard] and [makeLink] *)

Ltac inv_makeElement H := 
  match type of H with
  | makeElement _ _ _ _ _ _ = Some _ =>
      unfold makeElement in H ;
      unfold wrapElement in H ;  
      OptionUtils.monadInv H (* wrap has succeeded *) ;
      OptionUtils.monadInv H (* the user function succeeded also *) ;
      try discriminate ;
      inj H ;
      match goal with 
        [ W : ConcreteExpressions.wrap _ _ _  = Some _ |- _] =>
          repeat wrap_inv W 
      end
  end.


Ltac inv_makeGuard H :=
  match type of H with 
  | makeEmptyGuard _ _ _ = true =>
      unfold makeEmptyGuard in H ; 
      apply drop_true in H ;
      repeat wrap_inv H
             
  | makeGuard _ _ _ _  = true => 
      unfold makeGuard in H ;
      apply drop_true in H ;
      repeat wrap_inv H
  
  end.      

  
Ltac inv_makeLink H :=
  match type of H with
  | makeLink _ _ _ _ _ _ _ _ _ = Some _ =>
      unfold makeLink in H ;
      unfold wrapLink in H ;
      unfold ModelingMetamodel.toEData in H ;
      simpl (ModelingMetamodel.unbox _ _) in H; 
      let H2:= fresh "H" in
      match type of H with 
        _ <- ?E ; _ = Some _ => 
          destruct E eqn:H2 ; [ | discriminate H]
      end ;
      repeat wrap_inv H2 ;
      repeat OptionUtils.monadInv H 
  end.
