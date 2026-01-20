Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle : right_angle_triangle_spec 3 4 5 true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros _.
    left.
    (* 3*3 + 4*4 = 9 + 16 = 25 = 5*5 *)
    reflexivity.
  - intros _.
    reflexivity.
Qed.