Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_5_3_4 : right_angle_triangle_spec 5 3 4 true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros _.
    right. right.
    vm_compute.
    reflexivity.
  - intros _.
    reflexivity.
Qed.