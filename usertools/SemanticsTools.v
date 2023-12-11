Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.

Require Import TransformationConfiguration.
Require Import UserExpressions.

Require Import RichTraceLink.

Require Import Semantics.

Lemma in_modelElements_inv {tc:TransformationConfiguration} tr sm :
  forall e, In e (execute tr sm).(modelElements) <-> 
              exists s i n lp, 
                In 
                  {| 
                    source := (s, i, n);
                    produced := e ;
                    linkPattern := lp 
                  |} 
                  (compute_trace tr sm).
Proof.
  setoid_rewrite in_map_iff.
  intro ; split.
  + intros ([((?& ?) & ?) ? ?] &?&?).
    subst.
    repeat first [eexists | split | eassumption].
  + intros (?&?&?&?&?).
    repeat first [eexists | split | eassumption].
    reflexivity.
Qed.

Lemma in_modelLinks_inv {tc:TransformationConfiguration} tr sm :
  forall l, In l (execute tr sm).(modelLinks) <-> 
              exists s i n res lp,
                In 
                  {| 
                    source := (s, i, n);
                    produced := res ;
                    linkPattern := lp 
                  |} 
                  (compute_trace tr sm) 
                /\ In 
                     l 
                     (apply_link_pattern 
                        (compute_trace tr sm) 
                        sm 
                        {| 
                          source := (s, i, n);
                          produced := res ;
                          linkPattern := lp
                        |}).
Proof.
  setoid_rewrite in_flat_map at 1.
  intro ; split.
  + intros ([((?& ?) & ?) ? ?] &?&?). 
    repeat first [eexists | split | eassumption].
  + intros (?&?&?&?&?&?&?).
    repeat first [eexists | split | eassumption].
Qed.
