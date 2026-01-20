Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle : right_angle_triangle_spec 15 8 17 true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros _. left. reflexivity.
  - intros _. reflexivity.
Qed.