(**
 CoqTL user theorem: Column_name_uniqueness
 Def: if all attributes of the same class have unique names,
      then the generated columns of the same table
      have unique names.
 **)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.
Require Import core.utils.Utils.

(*Require Import core.Semantics.
Require Import core.Certification.*)
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

Require Import transformations.Class2Relational.Class2Relational.
Require Import transformations.Class2Relational.ClassMetamodel.
Require Import transformations.Class2Relational.RelationalMetamodel.

Theorem Column_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
    (* transformation *)
    rm = execute Class2Relational cm ->
    (* precondition *)
    (forall (at1: Attribute) (at2: Attribute) (cl: Class) (ats: list Attribute),
        In (ClassMetamodel.toObject AttributeClass at1) (allModelElements cm) ->
        In (ClassMetamodel.toObject AttributeClass at2) (allModelElements cm) ->
        In (ClassMetamodel.toObject ClassClass cl) (allModelElements cm) ->
        getClassAttributes cl cm = Some ats ->
        In at1 ats ->
        In at2 ats ->
        at1 <> at2 ->
        attr_name at1 <> attr_name at2) ->
    (* postcondition *)
    (forall (co1: Column) (co2: Column) (ta: Table) (cos: list Column),
        In (RelationalMetamodel.toObject ColumnClass co1) (allModelElements rm) ->
        In (RelationalMetamodel.toObject ColumnClass co2) (allModelElements rm) ->
        In (RelationalMetamodel.toObject TableClass ta) (allModelElements rm) ->
        getTableColumns ta rm = Some cos ->
        In co1 cos ->
        In co2 cos ->
        co1 <> co2 ->
        column_name co1 <> column_name co2).
Proof.
    intros.
    rewrite H in H1, H2, H3.
    rewrite (tr_execute_in_elements Class2Relational) in H1, H2, H3.
    do 2 destruct H1, H2, H3.
    destruct x, x0, x1.
    - contradiction.
    - contradiction.
    - contradiction.
    - contradiction.
    - contradiction.
    - contradiction.
    - contradiction.
    - (* [x::_] [y::_] [z::_] *) 
      destruct x, x0, x1.
      + (* [x] [y] [z] *)
        destruct o, o0, o1.  destruct c, c0, c1.
        * destruct g0. simpl in H8. destruct H8. inversion H8. contradiction.
        * destruct g0. simpl in H8. destruct H8. inversion H8. contradiction.
        * destruct g0. simpl in H8. destruct H8. inversion H8. contradiction.
        * destruct g0. simpl in H8. destruct H8. inversion H8. contradiction.
        * destruct g1. simpl in H9. destruct H9. inversion H9. contradiction.
        * destruct g1. simpl in H9. destruct H9. inversion H9. contradiction.
        * (* [a] [a] [c] *)
          specialize (H0 g g0 g1).
          remember (getClassAttributes g1 cm).
          destruct o.
          --specialize (H0 l).
            apply allTuples_incl in H1.
            apply allTuples_incl in H2.
            apply allTuples_incl in H3.
            unfold incl in H1, H2, H3.
            specialize (H1 (ClassMetamodel.toObject AttributeClass g)).
            specialize (H2 (ClassMetamodel.toObject AttributeClass g0)).
            specialize (H3 (ClassMetamodel.toObject ClassClass g1)).
            assert (In (ClassMetamodel.toObject AttributeClass g) [ClassMetamodel.toObject AttributeClass g]).
            { left. reflexivity. }
            assert (In (ClassMetamodel.toObject AttributeClass g0) [ClassMetamodel.toObject AttributeClass g0]).
            { left. reflexivity. }
            assert (In (ClassMetamodel.toObject ClassClass g1) [ClassMetamodel.toObject ClassClass g1]).
            { left. reflexivity. }
            assert (return l=return l). {reflexivity. }
            specialize (H0 (H1 H11) (H2 H12) (H3 H13) H14).
            destruct g, g0.
            destruct derived, derived0.
            ++ simpl in H8, H9, H10. contradiction.
            ++ simpl in H8, H9, H10. contradiction.
            ++ simpl in H8, H9, H10. contradiction.
            ++ simpl in H8, H9, H10. 
               destruct H8, H9, H10.
               ** apply rel_invert in H8.
                  apply rel_invert in H9.
                  apply rel_invert in H10.
                  rewrite <- H8.
                  rewrite <- H9.
                  unfold not.
                  intros.
                  inversion H15.
                  unfold column_name in H15.
                  rewrite H15 in H0.
                  simpl in H0.
                  admit.
               ** contradiction.
               ** contradiction.
               ** contradiction.
               ** contradiction.
               ** contradiction.
               ** contradiction.
               ** contradiction.
        -- admit.
    * destruct g1. destruct derived. 
      -- simpl in H10. contradiction. 
      -- simpl in H10. destruct H10. inversion H10. contradiction.
  + destruct o, o0, o1, o2. destruct c, c0, c1, c2; contradiction.
  + destruct o, o0, o1, o2. destruct c, c0, c1, c2; contradiction.
  + destruct o, o0, o1, o2. destruct c, c0, c1, c2; contradiction.
  + destruct o, o0, o1, o2. destruct c, c0, c1, c2; contradiction.
  + destruct o, o0, o1, o2. destruct c, c0, c1, c2; contradiction.
  + destruct o, o0, o1, o2. destruct c, c0, c1, c2; contradiction.
  + destruct o, o0, o1, o2. destruct c, c0, c1, c2; contradiction. 
 Admitted.


 


  



