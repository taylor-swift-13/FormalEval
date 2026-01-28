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

Example problem_9_test_case :
  problem_9_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z]
                 [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 5%Z; 5%Z; 5%Z; 5%Z].
Proof.
  unfold problem_9_spec.
  simpl.
  split.
  reflexivity.
  intros i Hi.
  destruct i as [|i1].
  simpl.
  split.
  intros j Hj.
  destruct j as [|j1].
  simpl; lia.
  exfalso; lia.
  exists 0%nat. split; [lia| simpl; reflexivity].
  destruct i1 as [|i2].
  simpl.
  split.
  intros j Hj.
  destruct j as [|j1].
  simpl; lia.
  destruct j1 as [|j2].
  simpl; lia.
  exfalso; lia.
  exists 1%nat. split; [lia| simpl; reflexivity].
  destruct i2 as [|i3].
  simpl.
  split.
  intros j Hj.
  destruct j as [|j1].
  simpl; lia.
  destruct j1 as [|j2].
  simpl; lia.
  destruct j2 as [|j3].
  simpl; lia.
  exfalso; lia.
  exists 2%nat. split; [lia| simpl; reflexivity].
  destruct i3 as [|i4].
  simpl.
  split.
  intros j Hj.
  destruct j as [|j1].
  simpl; lia.
  destruct j1 as [|j2].
  simpl; lia.
  destruct j2 as [|j3].
  simpl; lia.
  destruct j3 as [|j4].
  simpl; lia.
  exfalso; lia.
  exists 3%nat. split; [lia| simpl; reflexivity].
  destruct i4 as [|i5].
  simpl.
  split.
  intros j Hj.
  destruct j as [|j1].
  simpl; lia.
  destruct j1 as [|j2].
  simpl; lia.
  destruct j2 as [|j3].
  simpl; lia.
  destruct j3 as [|j4].
  simpl; lia.
  destruct j4 as [|j5].
  simpl; lia.
  exfalso; lia.
  exists 4%nat. split; [lia| simpl; reflexivity].
  destruct i5 as [|i6].
  simpl.
  split.
  intros j Hj.
  destruct j as [|j1].
  simpl; lia.
  destruct j1 as [|j2].
  simpl; lia.
  destruct j2 as [|j3].
  simpl; lia.
  destruct j3 as [|j4].
  simpl; lia.
  destruct j4 as [|j5].
  simpl; lia.
  destruct j5 as [|j6].
  simpl; lia.
  exfalso; lia.
  exists 4%nat. split; [lia| simpl; reflexivity].
  destruct i6 as [|i7].
  simpl.
  split.
  intros j Hj.
  destruct j as [|j1].
  simpl; lia.
  destruct j1 as [|j2].
  simpl; lia.
  destruct j2 as [|j3].
  simpl; lia.
  destruct j3 as [|j4].
  simpl; lia.
  destruct j4 as [|j5].
  simpl; lia.
  destruct j5 as [|j6].
  simpl; lia.
  destruct j6 as [|j7].
  simpl; lia.
  exfalso; lia.
  exists 4%nat. split; [lia| simpl; reflexivity].
  destruct i7 as [|i8].
  simpl.
  split.
  intros j Hj.
  destruct j as [|j1].
  simpl; lia.
  destruct j1 as [|j2].
  simpl; lia.
  destruct j2 as [|j3].
  simpl; lia.
  destruct j3 as [|j4].
  simpl; lia.
  destruct j4 as [|j5].
  simpl; lia.
  destruct j5 as [|j6].
  simpl; lia.
  destruct j6 as [|j7].
  simpl; lia.
  destruct j7 as [|j8].
  simpl; lia.
  exfalso; lia.
  exists 4%nat. split; [lia| simpl; reflexivity].
  destruct i8 as [|i9].
  simpl.
  split.
  intros j Hj.
  destruct j as [|j1].
  simpl; lia.
  destruct j1 as [|j2].
  simpl; lia.
  destruct j2 as [|j3].
  simpl; lia.
  destruct j3 as [|j4].
  simpl; lia.
  destruct j4 as [|j5].
  simpl; lia.
  destruct j5 as [|j6].
  simpl; lia.
  destruct j6 as [|j7].
  simpl; lia.
  destruct j7 as [|j8].
  simpl; lia.
  destruct j8 as [|j9].
  simpl; lia.
  exfalso; lia.
  exists 4%nat. split; [lia| simpl; reflexivity].
  exfalso; lia.
Qed.