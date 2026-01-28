Require Import ZArith.
Require Import Bool.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_float : right_angle_triangle_spec 94.82545294464254 26.117120159873124 94.48837938393268 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H. discriminate H.
  - intros [H | [H | H]]; lra.
Qed.