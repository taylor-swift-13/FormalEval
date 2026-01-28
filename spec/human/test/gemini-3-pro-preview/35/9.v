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

Example test_case_35 : problem_35_spec [1.5; 3; 2; -4; -3.5; 0; 2.5] 3.
Proof.
  unfold problem_35_spec.
  split.
  
  - (* Subgoal 1: In 3 [1.5; 3; ...] *)
    simpl.
    right. left. reflexivity.
    
  - (* Subgoal 2: forall x, In x [...] -> x <= 3 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    + (* Case 1.5 = x *)
      rewrite <- H. lra.
    + (* Case 3 = x *)
      rewrite <- H. lra.
    + (* Case 2 = x *)
      rewrite <- H. lra.
    + (* Case -4 = x *)
      rewrite <- H. lra.
    + (* Case -3.5 = x *)
      rewrite <- H. lra.
    + (* Case 0 = x *)
      rewrite <- H. lra.
    + (* Case 2.5 = x *)
      rewrite <- H. lra.
    + (* Case False *)
      contradiction.
Qed.