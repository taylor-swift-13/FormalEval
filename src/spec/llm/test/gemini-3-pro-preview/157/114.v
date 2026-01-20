Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_25_60_65 : right_angle_triangle_spec 25 60 65 true.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - (* -> direction *)
    intros _.
    left.
    (* Verify 25^2 + 60^2 = 65^2 *)
    vm_compute.
    reflexivity.
  - (* <- direction *)
    intros _.
    reflexivity.
Qed.