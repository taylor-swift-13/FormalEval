Require Import List Reals.
Require Import Lia.
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

Example test_case_0: 
  problem_0_spec [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] 0.3 true.
Proof.
  unfold problem_0_spec.
  split.
  - (* -> direction *)
    intros [i [j [x [y [Hneq [Hi [Hj [Hx [Hy Habs]]]]]]]]].
    reflexivity.
  - (* <- direction *)
    intros Hout.
    inversion Hout; subst.
    exists (1%nat), (5%nat), 2.0, 2.2.
    repeat split.
    + discriminate.
    + simpl; lia.
    + simpl; lia.
    + simpl; reflexivity.
    + simpl; reflexivity.
    + unfold Rabs.
      simpl.
      rewrite Rabs_right.
      * lra.
      * apply Rle_ge.
        lra.
Qed.