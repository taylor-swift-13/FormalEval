Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example problem_42_test_empty : problem_42_spec [] [].
Proof.
  unfold problem_42_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi. exfalso. lia.
Qed.