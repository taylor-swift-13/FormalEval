Require Import List ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example problem_9_test_case : problem_9_spec [] [].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i. intros H.
    inversion H.
Qed.