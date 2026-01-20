Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_15_8_17 : right_angle_triangle_spec 15 8 17 true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - (* -> direction *)
    intros _.
    left.
    (* Verify 15^2 + 8^2 = 17^2 *)
    vm_compute.
    reflexivity.
  - (* <- direction *)
    intros _.
    reflexivity.
Qed.