Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_9_pre : Prop := True.

Definition problem_9_spec (input output : list Z) :=
  length output = length input /\
  forall i,
    (i < length output)%nat ->
    (forall j, (j <= i)%nat -> nth j input 0 <= nth i output 0) /\
    (exists j, (j <= i)%nat /\ nth j input 0 = nth i output 0).

Example test_case_negatives : problem_9_spec [-1; -2; -3; -4; -5; -4; -3; -2; -1] [-1; -1; -1; -1; -1; -1; -1; -1; -1].
Proof.
  unfold problem_9_spec.
  split.
  - reflexivity.
  - intros i Hi.
    assert (H_bound: (i < 9)%nat). { simpl in Hi. lia. }
    assert (H_out: nth i [-1; -1; -1; -1; -1; -1; -1; -1; -1] 0 = -1).
    { do 9 (destruct i; [ reflexivity | ]). lia. }
    rewrite H_out.
    split.
    + intros j Hj.
      do 9 (destruct j; [ simpl; lia | ]).
      lia.
    + exists 0%nat. split.
      * lia.
      * reflexivity.
Qed.