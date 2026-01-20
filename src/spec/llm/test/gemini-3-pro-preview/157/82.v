Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_5_22_21 : right_angle_triangle_spec 5 22 21 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - (* -> direction *)
    intros H.
    discriminate H.
  - (* <- direction *)
    intros [H | [H | H]]; vm_compute in H; discriminate H.
Qed.