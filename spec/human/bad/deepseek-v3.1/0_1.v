Require Import List Reals Arith.
Import ListNotations.
Open Scope R_scope.

Definition problem_0_pre(threshold : R): Prop :=
  threshold >= 0.

Definition problem_0_spec (numbers : list R) (threshold : R) (output : bool): Prop :=
  (exists (i j : nat) (x y : R),
    i <> j /\
    Nat.lt i (length numbers) /\
    Nat.lt j (length numbers) /\
    nth i numbers 0 = x /\
    nth j numbers 0 = y /\
    Rabs (x - y) <= threshold) <->
    output = true.

Example test_case : 
  problem_0_spec [1.0%R; 2.0%R; 3.9%R; 4.0%R; 5.0%R; 2.2%R] 0.3%R true.
Proof.
  unfold problem_0_spec.
  split.
  - intros H.
    reflexivity.
  - intros H.
    exists 1%nat, 5%nat.
    exists 2.0%R, 2.2%R.
    repeat split.
    + discriminate.
    + simpl. apply lt_0_Sn.
    + simpl. unfold lt. apply le_n_S. apply le_n_S. apply le_n_S. apply le_n_S. apply le_n_S. apply le_0_n.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + compute.
      unfold Rabs.
      destruct Rcase_abs as [H1|H1].
      * lra.
      * lra.
Qed.