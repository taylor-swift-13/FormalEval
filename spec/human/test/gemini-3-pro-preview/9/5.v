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

Example test_case_1 : problem_9_spec [1; 1; 1; 1; 1] [1; 1; 1; 1; 1].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    split.
    + intros j Hj.
      repeat (destruct i as [|i]; [|try lia]).
      all: repeat (destruct j as [|j]; [|try lia]).
      all: simpl; lia.
    + exists i.
      split; [auto|].
      repeat (destruct i as [|i]; [|try lia]).
      all: simpl; reflexivity.
Qed.