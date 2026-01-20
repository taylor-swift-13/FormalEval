Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

Example test_simplify_1 : simplify_spec 921 7939 8 113 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_contra.
    discriminate.
  - intros H_mod.
    compute in H_mod.
    discriminate.
Qed.