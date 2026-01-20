Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (result : bool) : Prop :=
  result = true <->
    (a * a + b * b = c * c \/
     a * a + c * c = b * b \/
     b * b + c * c = a * a).

Example right_angle_triangle_test :
  right_angle_triangle_spec 3%Z 4%Z 5%Z true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros _. left. vm_compute. reflexivity.
  - intros _. reflexivity.
Qed.