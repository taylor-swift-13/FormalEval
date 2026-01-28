Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_25_60_65 : right_angle_triangle_spec 25 60 65 true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros _.
    left.
    simpl.
    reflexivity.
  - intros _.
    reflexivity.
Qed.