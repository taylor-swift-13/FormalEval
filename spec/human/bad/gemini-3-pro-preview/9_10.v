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

Example test_case_1 : problem_9_spec [10; 20; 30; 40; 50] [10; 20; 30; 40; 50].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    repeat (destruct i as [|i]; [| try lia]);
    split.
    + intros j Hj.
      repeat (destruct j as [|j]; [| try lia]);
      simpl; lia.
    + eexists. split.
      2: simpl; reflexivity.
      lia.
Qed.