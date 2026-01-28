Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_17_2022_1 : right_angle_triangle_spec 17 2022 1 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H.
    discriminate H.
  - intros [H | [H | H]]; simpl in H; try discriminate; try lia.
Qed.