Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_12_11_13 : right_angle_triangle_spec 12 11 13 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    lia.
Qed.