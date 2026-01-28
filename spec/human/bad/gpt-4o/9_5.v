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

Example problem_9_test_case : problem_9_spec [1%Z; 1%Z; 1%Z; 1%Z; 1%Z] [1%Z; 1%Z; 1%Z; 1%Z; 1%Z].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i. intros H.
    split.
    + intros j Hj.
      apply nth_In with (d := 0%Z) in Hj.
      apply nth_In with (d := 0%Z) in H.
      rewrite nth_indep with (d := 0%Z) in Hj; try assumption.
      rewrite nth_indep with (d := 0%Z) in H; try assumption.
      rewrite nth_indep with (d := 0%Z) in H; try assumption.
      assumption.
    + exists i. split.
      * apply le_n.
      * reflexivity.
Qed.