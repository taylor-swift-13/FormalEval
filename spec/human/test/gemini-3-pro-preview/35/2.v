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

Example test_case_35 : problem_35_spec [5; 3; -5; 2; -3; 3; 9; 0; 124; 1; -10] 124.
Proof.
  unfold problem_35_spec.
  split.
  - simpl. tauto.
  - intros x H.
    simpl in H.
    repeat destruct H as [H | H]; try lia.
Qed.