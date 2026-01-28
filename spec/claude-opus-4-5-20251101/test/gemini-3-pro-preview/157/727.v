Require Import Reals.
Require Import Bool.
Require Import Psatz.

Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_26_94_94 : right_angle_triangle_spec 26.117120159873124 94.48837938393268 94.48837938393268 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H. discriminate.
  - intros [H | [H | H]]; nra.
Qed.