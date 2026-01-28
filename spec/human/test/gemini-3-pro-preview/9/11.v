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

Example test_case_decreasing : problem_9_spec [50%Z; 40%Z; 30%Z; 20%Z; 10%Z] [50%Z; 50%Z; 50%Z; 50%Z; 50%Z].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    repeat (destruct i as [|i]; [| simpl in H; try lia]).
    all: split.
    all: try (intros j Hj; repeat (destruct j as [|j]; [| simpl in Hj; try lia]); simpl; lia).
    all: exists 0%nat; split; [lia | reflexivity].
Qed.