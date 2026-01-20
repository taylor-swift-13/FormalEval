Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_24_16_16 : right_angle_triangle_spec 24 16 16 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H.
    discriminate.
  - intros [H | [H | H]]; vm_compute in H; discriminate.
Qed.