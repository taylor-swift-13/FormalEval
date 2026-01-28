Require Import Reals.
Require Import Bool.
Require Import Psatz.

Open Scope R_scope.

Definition right_angle_triangle_spec (a b c : R) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_float : right_angle_triangle_spec 24.71115668501026 93.15108572417166 93.65019636949225 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H.
    discriminate.
  - intros [H | [H | H]]; lra.
Qed.