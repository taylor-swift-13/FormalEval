Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle : right_angle_triangle_spec 3 4 5 true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros _.
    left.
    reflexivity.
  - intros _.
    reflexivity.
Qed.