Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


(*************************************************************)
(** * Universality                                           *)
(*************************************************************)

Definition toTransformation (tc: TransformationConfiguration) (f: SourceModel -> TargetModel) := 
  (buildTransformation 0 [
    (buildRule "rule"%string 
      (fun sm sp => match sp with nil => true | _ => false end)
      (fun sm sp => Some (length ((f sm).(modelElements))))
      [(buildOutputPatternUnit "out"%string 
         (fun i sm sp => nth_error ((f sm).(modelElements)) i)
         (fun tls i sm sp te => match i with 0 => Some (f sm).(modelLinks) | _ => None end))
      ])
  ]).

Theorem universality :
forall (tc: TransformationConfiguration) (f: SourceModel -> TargetModel),
  (forall (sm: SourceModel), Model_wellFormed sm -> Model_wellFormed (f sm)) ->
  exists (t: Transformation), 
    forall (sm: SourceModel), Model_wellFormed sm -> execute t sm = f sm.
Proof.
  intros.
  exists (toTransformation tc f).
  intros.
  unfold execute.
  unfold applyTrOnModel.
  unfold applyTrOnPiece.
  unfold applyRuleOnPiece.
  unfold applyIterationOnPiece.
  unfold applyUnitOnPiece.
  unfold EvalUserExpressions.evalOutputPatternLink.
  unfold instantiateTrOnModel.
  unfold instantiateTrOnPiece.
  unfold traceTrOnModel.
  unfold traceTrOnPiece.
  unfold traceRuleOnPiece.
  unfold traceIterationOnPiece.
  unfold traceElementOnPiece.
  unfold EvalUserExpressions.evalOutputPatternElement.
  unfold EvalUserExpressions.evalIterator.
  simpl.
  repeat rewrite <- app_nil_end.
  rewrite map_flat_map.
  apply (H sm) in H0.
  destruct (f sm). simpl.
  f_equal.
  - clear H. clear H0.
    induction modelElements.
    * reflexivity.
    * simpl.
      f_equal.
      rewrite <- IHmodelElements at 2.
      repeat rewrite flat_map_concat_map.
      f_equal.
      rewrite <- seq_shift.
      rewrite map_map.
      (* The two are equals because of the projection [produced]. *)
      simpl nth_error.
      apply map_ext ; intro x.
      repeat rewrite <- app_nil_end.
      repeat rewrite <- optionToList_map.
      f_equal.
      repeat rewrite OptionUtils.option_map_bind.
      simpl (produced _).
      reflexivity.
  - destruct modelElements eqn:dst.
    * crush. 
    * clear H0.
      simpl. 
      repeat rewrite app_nil_r.
      rewrite app_nil_end.
      f_equal.
      apply in_flat_map_nil.
      intros.
      rewrite app_nil_r.
      destruct a.
      + exfalso. 
        rewrite in_seq in H0.
        lia.
      + simpl.
        rewrite in_seq in H0.
        destruct H0.
        simpl in H1.
        apply Lt.lt_S_n in H1.
        destruct (nth_error l a); reflexivity.
Qed.
