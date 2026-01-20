Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

Example test_simplify_2 : simplify_spec 943 29 9176 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_contra.
    discriminate H_contra.
  - intros H_mod.
    vm_compute in H_mod.
    discriminate H_mod.
Qed.