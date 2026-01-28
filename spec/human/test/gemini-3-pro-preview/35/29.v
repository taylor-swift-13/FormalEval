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

Example test_case_35 : problem_35_spec [-5; 2; 9; 5; 6; 7; 2] 9.
Proof.
  unfold problem_35_spec.
  split.
  - (* Prove 9 is in the list *)
    simpl.
    tauto.
  - (* Prove 9 is the maximum element *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    + (* x = -5 *)
      lia.
    + (* x = 2 *)
      lia.
    + (* x = 9 *)
      lia.
    + (* x = 5 *)
      lia.
    + (* x = 6 *)
      lia.
    + (* x = 7 *)
      lia.
    + (* x = 2 *)
      lia.
    + (* False *)
      contradiction.
Qed.