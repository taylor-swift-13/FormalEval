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

Example test_case_35 : problem_35_spec [-1; -2; -3; -4; 100; -3] 100.
Proof.
  unfold problem_35_spec.
  split.
  
  - (* Subgoal 1: In 100 ... *)
    simpl.
    tauto.
    
  - (* Subgoal 2: forall x, In x ... -> x <= 100 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + (* -1 *) lia.
    + (* -2 *) lia.
    + (* -3 *) lia.
    + (* -4 *) lia.
    + (* 100 *) lia.
    + (* -3 *) lia.
    + (* False *) contradiction.
Qed.