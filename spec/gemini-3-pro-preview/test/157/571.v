Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition right_angle_triangle_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> 
  (a ^ 2 + b ^ 2 = c ^ 2 \/ a ^ 2 + c ^ 2 = b ^ 2 \/ b ^ 2 + c ^ 2 = a ^ 2).

Example test_right_angle_triangle_457_12_139 : right_angle_triangle_spec 457 12 139 false.
Proof.
  unfold right_angle_triangle_spec.
  split.
  - (* -> direction *)
    intros H.
    inversion H.
  - (* <- direction *)
    intros H.
    vm_compute in H.
    destruct H as [H1 | [H2 | H3]]; discriminate.
Qed.