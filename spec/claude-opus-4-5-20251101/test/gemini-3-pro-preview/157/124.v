Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_495_226_226 : right_angle_triangle_spec 495 226 226 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    simpl in H.
    lia.
Qed.