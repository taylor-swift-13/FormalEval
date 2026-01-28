Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example test_right_angle_triangle_2021_2_2020 : right_angle_triangle_spec 2021 2 2020 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intro H. discriminate.
  - intro H.
    destruct H as [H | [H | H]];
    vm_compute in H;
    lia.
Qed.