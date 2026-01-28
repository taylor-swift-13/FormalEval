Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Psatz.
Import ListNotations.
Open Scope R_scope.

(* Pre: input must be non-empty *)
Definition problem_35_pre (input : list R) : Prop := input <> []%list.

Definition problem_35_spec (input : list R) (output : R) : Prop :=
  In output input /\
  forall x, In x input -> x <= output.

Example test_case_35 : problem_35_spec [1.5; 3; 2; -3.5; 0] 3.
Proof.
  unfold problem_35_spec.
  split.
  
  - (* Subgoal 1: In 3 [1.5; 3; 2; -3.5; 0] *)
    simpl.
    right; left; reflexivity.
    
  - (* Subgoal 2: forall x, In x ... -> x <= 3 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + lra.
    + lra.
    + lra.
    + lra.
    + lra.
    + contradiction.
Qed.