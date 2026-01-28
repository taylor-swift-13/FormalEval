Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_8_11_12 : right_angle_triangle_spec 8 11 12 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - (* false = true -> ... *)
    intros H.
    discriminate H.
  - (* ... -> false = true *)
    intros [H | [H | H]].
    + (* 8^2 + 11^2 = 12^2 *)
      vm_compute in H.
      discriminate H.
    + (* 8^2 + 12^2 = 11^2 *)
      vm_compute in H.
      discriminate H.
    + (* 11^2 + 12^2 = 8^2 *)
      vm_compute in H.
      discriminate H.
Qed.