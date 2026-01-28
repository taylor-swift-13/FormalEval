Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Psatz. (* Imports lia tactic for integer arithmetic *)
Import ListNotations.
Open Scope Z_scope.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list Z) : Prop := input <> []%list.

Definition problem_35_spec (input : list Z) (output : Z) : Prop :=
  In output input /\
  forall x, In x input -> (x <= output)%Z.

Example test_case_35 : problem_35_spec [49; 49; 49; 47; 47; 47] 49.
Proof.
  (* Unfold the specification to expose the logical structure *)
  unfold problem_35_spec.
  
  (* Split the goal into two parts *)
  split.
  
  - (* Subgoal 1: Prove 49 is in the list *)
    simpl.
    tauto.
    
  - (* Subgoal 2: Prove that for any x in the list, x <= 49 *)
    intros x H.
    simpl in H.
    (* Destruct the disjunctions arising from the list membership *)
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]]; try lia; try contradiction.
Qed.