Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_495_58_65 : right_angle_triangle_spec 495 58 65 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - intros H. discriminate H.
  - intros [H1 | [H2 | H3]].
    + vm_compute in H1. discriminate H1.
    + vm_compute in H2. discriminate H2.
    + vm_compute in H3. discriminate H3.
Qed.