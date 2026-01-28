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

Example test_case_1 : problem_9_spec [1; 2; 3; 2; 1; 2; 3; 2; 1] [1; 2; 3; 3; 3; 3; 3; 3; 3].
Proof.
  unfold problem_9_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [| try (simpl in H; lia)]).
    + split.
      * intros j Hj; repeat (destruct j as [|j]; [| try lia]); simpl; lia.
      * exists 0%nat. split; [lia|reflexivity].
    + split.
      * intros j Hj; repeat (destruct j as [|j]; [| try lia]); simpl; lia.
      * exists 1%nat. split; [lia|reflexivity].
    + split.
      * intros j Hj; repeat (destruct j as [|j]; [| try lia]); simpl; lia.
      * exists 2%nat. split; [lia|reflexivity].
    + split.
      * intros j Hj; repeat (destruct j as [|j]; [| try lia]); simpl; lia.
      * exists 2%nat. split; [lia|reflexivity].
    + split.
      * intros j Hj; repeat (destruct j as [|j]; [| try lia]); simpl; lia.
      * exists 2%nat. split; [lia|reflexivity].
    + split.
      * intros j Hj; repeat (destruct j as [|j]; [| try lia]); simpl; lia.
      * exists 2%nat. split; [lia|reflexivity].
    + split.
      * intros j Hj; repeat (destruct j as [|j]; [| try lia]); simpl; lia.
      * exists 2%nat. split; [lia|reflexivity].
    + split.
      * intros j Hj; repeat (destruct j as [|j]; [| try lia]); simpl; lia.
      * exists 2%nat. split; [lia|reflexivity].
    + split.
      * intros j Hj; repeat (destruct j as [|j]; [| try lia]); simpl; lia.
      * exists 2%nat. split; [lia|reflexivity].
Qed.