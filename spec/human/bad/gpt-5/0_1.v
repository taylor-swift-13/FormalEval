Require Import List Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
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

Example problem_0_test_case :
  problem_0_spec [1.0%R; 2.0%R; 3.9%R; 4.0%R; 5.0%R; 2.2%R] 0.3%R true.
Proof.
  unfold problem_0_spec.
  split.
  - intros _. reflexivity.
  - intros _. exists (2%nat), (3%nat), (3.9%R), (4.0%R).
    repeat split.
    + lia.
    + simpl. lia.
    + simpl. lia.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + apply Rabs_le_inv. split; lra.
Qed.