Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_13_457_457 : right_angle_triangle_spec 13 457 457 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intro H.
    discriminate H.
  - intro H.
    destruct H as [H | [H | H]]; lia.
Qed.