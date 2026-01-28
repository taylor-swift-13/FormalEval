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

Example test_case_1 : problem_9_spec [-1; -2; -3; -4; -5; -3; -2; -1] [-1; -1; -1; -1; -1; -1; -1; -1].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    assert (Ho: nth i [-1; -1; -1; -1; -1; -1; -1; -1] 0 = -1).
    { do 8 (destruct i as [|i]; [reflexivity|]). lia. }
    rewrite Ho.
    split.
    + intros j Hj.
      do 8 (destruct j as [|j]; [simpl; lia|]).
      lia.
    + exists 0%nat.
      split.
      * lia.
      * simpl. reflexivity.
Qed.