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

From transformations.Class2Relational Require Tactics.

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
    repeat Tactics.show_singleton.
    
    simpl RelationalMetamodel.toObject in *.
    simpl ClassMetamodel.toObject in *.
    repeat Tactics.show_origin. 

          specialize (H0 a a0 c).
          remember (getClassAttributes c cm).
          destruct o.
          --specialize (H0 l).
            apply allTuples_incl in H1.
            apply allTuples_incl in H2.
            apply allTuples_incl in H3.
            unfold incl in H1, H2, H3.
            specialize (H1 (ClassMetamodel.toObject AttributeClass a0)).
            specialize (H2 (ClassMetamodel.toObject AttributeClass a)).
            specialize (H3 (ClassMetamodel.toObject ClassClass c)).
            assert (In (ClassMetamodel.toObject AttributeClass a) [ClassMetamodel.toObject AttributeClass a]).
            { left. reflexivity. }
            assert (In (ClassMetamodel.toObject AttributeClass a0) [ClassMetamodel.toObject AttributeClass a0]).
            { left. reflexivity. }
            assert (In (ClassMetamodel.toObject ClassClass c) [ClassMetamodel.toObject ClassClass c]).
            { left. reflexivity. }
            assert (return l=return l). {reflexivity. }
            specialize (H0 (H2 H11) (H1 H12) (H3 H13) H14).
            destruct a, a0.
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
    
 Admitted.


 


  



