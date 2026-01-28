Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_457_110_10002 : right_angle_triangle_spec 457 110 10002 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H.
    discriminate H.
  - intros [H | [H | H]]; lia.
Qed.