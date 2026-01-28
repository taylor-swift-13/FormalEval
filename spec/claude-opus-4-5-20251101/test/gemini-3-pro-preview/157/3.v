Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_10_6_8 : right_angle_triangle_spec 10 6 8 true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros _.
    right. right.
    simpl.
    reflexivity.
  - intros _.
    reflexivity.
Qed.