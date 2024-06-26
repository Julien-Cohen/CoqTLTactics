Require Import core.Semantics.

Import 
  Metamodel Model NotationUtils List core.TransformationConfiguration.

From usertools 
  Require 
  SemanticsTools 
  ChoiceTools 
  ConcreteExpressionTools 
  SyntaxTools
  ConcreteSyntaxTools.

(** * FW Tactics on traces *)

(** ** Tactics that fully unfold [In _ compute_trace _ _] and solve easy goals. *) 

(** Takes as parameter the index of the rule, the index of the output pattern in that rule, and a tactics that refers to the source element hypotheses. *)

Ltac in_compute_trace_inv_any_fw r_name pat_name incl_tac :=
      
      (* Precondition on the goal. *)
      match goal with 
      | [ |- List.In _ (compute_trace ?T _)] => 
                    
          SemanticsTools.in_compute_trace_inv_tac ;

          (* 7 goals *)
          [ | | | | | | ] ;


          [ (* Fix the rule under concern following user hint *)
            solve [ChoiceTools.rule_named r_name] 
                  
          | (* Fix the output pattern in the rule following user hint *)
            solve [ChoiceTools.pattern_named pat_name] 
                  
          | (* Fix the source piece (any size) *)
            incl_tac
                                                   
          | (* The guard goal may rely on user expressions and can be arbitrary difficult to prove *)
            simpl
              
          | (* arity *) 
            solve [simpl ; auto] 
              
          | (* iteration counter *)
            solve [simpl ; auto ] 
                  
          | (* The make_element goal relies on user expressions and can be arbitrary difficult to prove *) 
            simpl 

          ] 

      end ;

  (* Post-condition *)
  [ | ] (* the guard and the makeElement goals remain. *). 



(** Instance for singleton patterns (patterns of size 1) *)
Ltac in_compute_trace_inv_singleton_fw r_name pat_name H :=
  in_compute_trace_inv_any_fw 
    r_name 
    pat_name 
    ltac:(ListUtils.solve_incl_singleton H).

(** Instance for pair patterns (patterns of size 2) *)
Ltac in_compute_trace_inv_pair_fw r_name pat_name H1 H2 :=
  in_compute_trace_inv_any_fw 
    r_name 
    pat_name 
    ltac:(ListUtils.solve_incl_pair H1 H2).

(** Instance for triple patterns (patterns of size 3) *)
Ltac in_compute_trace_inv_triple_fw r_name pat_name H1 H2 H3 :=
  in_compute_trace_inv_any_fw 
    r_name 
    pat_name 
    ltac:(ListUtils.solve_incl_triple H1 H2 H3).

(** Instance for patterns of size 4 *)
Ltac in_compute_trace_inv_4_fw r_name pat_name H1 H2 H3 H4 :=
  in_compute_trace_inv_any_fw 
    r_name 
    pat_name 
    ltac:(ListUtils.solve_incl_4 H1 H2 H3 H4).

(** Instance for patterns of size 5 *)
Ltac in_compute_trace_inv_5_fw r_name pat_name H1 H2 H3 H4 H5 :=
  in_compute_trace_inv_any_fw 
    r_name 
    pat_name 
    ltac:(ListUtils.solve_incl_5 H1 H2 H3 H4 H5).



(** * FW tactics on Elements and Links *)

(** *** On elements (singletons, then pairs and triples) *)

Ltac in_modelElements_singleton_fw_tac r_name pat_name i H :=

      (* Precondition on H. *)
      match type of H with 
      | List.In _ ?M.(modelElements) => 
          (* Precondition on the goal *)
          match goal with 
            [ |- List.In _ (execute ?T M).(modelElements) ] => idtac
          end
      end ;
      
      apply <- SemanticsTools.in_modelElements_inv ; 
      
      eexists ; exists i ; eexists ; eexists ; 
      
      in_compute_trace_inv_singleton_fw r_name pat_name H ;
            
      (* Post-condition. *)
      [ | ] .


Ltac in_modelElements_pair_fw_tac r_named pat_name i H1 H2 :=
  (* Precondition on H1. *)
  match type of H1 with 
    List.In _ ?M.(modelElements) =>
      
      (* Precondition on H2. *)
      match type of H2 with 
        List.In _ M.(modelElements) =>
          
          (* Precondition on the goal. *)
          match goal with 
          | [ |- In _ (execute _ M).(modelElements) ] => idtac
          end
      end
  end ;
  apply <- SemanticsTools.in_modelElements_inv ; 
  
  eexists ; exists i ; eexists ; eexists ; 
  
  in_compute_trace_inv_pair_fw r_named pat_name H1 H2 ;
                               
                               
  (* Post-condition *)
  [ | ].

 Ltac in_modelElements_triple_fw_tac r_named pat_name i H1 H2 H3 :=
  (* Precondition on H1. *)
  match type of H1 with 
    List.In _ ?M.(modelElements) =>
      
      (* Precondition on H2. *)
      match type of H2 with 
        List.In _ M.(modelElements) =>
      (* Precondition on H3. *)
          match type of H3 with 
            List.In _ M.(modelElements) =>
              
              (* Precondition on the goal. *)
              match goal with 
              | [ |- In _ (execute _ M).(modelElements) ] => idtac
              end
          end
      end 
  end;
  apply <- SemanticsTools.in_modelElements_inv ; 
  
  eexists ; exists i ; eexists ; eexists ; 
  
  in_compute_trace_inv_triple_fw r_named pat_name H1 H2 H3;
                               
                               
  (* Post-condition *)
  [ | ].
 

Ltac in_modelElements_4_fw_tac r_named pat_name i H1 H2 H3 H4 :=
  (* Precondition on H1. *)
  match type of H1 with 
    List.In _ ?M.(modelElements) =>
      
      (* Precondition on H2. *)
      match type of H2 with 
        List.In _ M.(modelElements) =>

          (* Precondition on H3. *)
          match type of H3 with 
            List.In _ M.(modelElements) =>

             (* Precondition on H4. *)
             match type of H4 with 
               List.In _ M.(modelElements) =>
              
                (* Precondition on the goal. *)
                match goal with 
                | [ |- In _ (execute _ M).(modelElements) ] => idtac
                end
             end 
          end
      end 
  end;

  apply <- SemanticsTools.in_modelElements_inv ; 
  
  eexists ; exists i ; eexists ; eexists ; 
  
  in_compute_trace_inv_4_fw r_named pat_name H1 H2 H3 H4 ;
                               
                               
  (* Post-condition *)
  [ | ].
 
Ltac in_modelElements_5_fw_tac r_named pat_name i H1 H2 H3 H4 H5 :=
  (* Precondition on H1. *)
  match type of H1 with 
    List.In _ ?M.(modelElements) =>
      
      (* Precondition on H2. *)
      match type of H2 with 
        List.In _ M.(modelElements) =>

          (* Precondition on H3. *)
          match type of H3 with 
            List.In _ M.(modelElements) =>

             (* Precondition on H4. *)
             match type of H4 with 
               List.In _ M.(modelElements) =>
              
               (* Precondition on H5. *)
               match type of H5 with 
                 List.In _ M.(modelElements) =>
              
                  (* Precondition on the goal. *)
                  match goal with 
                  | [ |- In _ (execute _ M).(modelElements) ] => idtac
                  end
              end
             end 
          end
      end 
  end;

  apply <- SemanticsTools.in_modelElements_inv ; 
  
  eexists ; exists i ; eexists ; eexists ; 
  
  in_compute_trace_inv_5_fw r_named pat_name H1 H2 H3 H4 H5 ;
                               
                               
  (* Post-condition *)
  [ | ].
 

(** *** On links (singleton) *)

Ltac transform_link_fw_tac_singleton r_name pat_name i H :=

  (* Precondition on H. *)
  match type of H with 
    List.In _ ?M.(modelElements) =>

      (* Precondition on the goal. *)
      match goal with
        [ |- In _ (execute _ M).(modelLinks) ] => idtac
      end 
  end  ;
  
  apply <- SemanticsTools.in_modelLinks_inv ; 
  
  eexists ; exists i ; eexists ; eexists ; eexists ; 
  
  split ; 
  
  [ in_compute_trace_inv_singleton_fw r_name pat_name H | ] ;
  
  autounfold with 
    parse ConcreteOutputPatternUnit_accessors opu_accessors ;
  
  
  (* Post-condition *)
  [ | | ].


(** * Simple tactics (for simple situations) *)
(** Deprecated *)

(** A simple FW tactic for elements (lemma + tactic) (only
    singleton patterns).  The drawback of this lemma/tactic
    is that when the traceTrOnPiece premise is not solved by
    auto, it leaves the user with a painful subgoal on traces. *)
Lemma transform_element_fw {tc} (t:Syntax.Transformation (tc:=tc)) cm e te  :
  0 < Syntax.arity t ->
  In e cm.(modelElements) ->
  In te (produced_elements (traceTrOnPiece t cm [e])) ->
  In te (execute t cm).(modelElements).
Proof.
  intros A IN1 IN2.
  simpl.
  unfold compute_trace, produced_elements.
  rewrite ListUtils.map_flat_map. (* a trace can have several target elements *)
  apply List.in_flat_map. (* this is doing the job *)
  exists ([e]) ; split ; [ | auto ].
  apply <- SemanticsTools.in_allTuples_singleton. auto.
Qed.

Ltac transform_element_fw_tac :=
  match goal with
    [ |- In _ (execute ?T _).(modelElements) ] =>
      eapply (transform_element_fw T) ; 
      [ solve [ simpl ; auto ] 
      | eassumption 
      | try (solve [simpl;auto])]
  end.

