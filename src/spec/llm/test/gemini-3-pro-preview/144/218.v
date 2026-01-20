Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

Example test_simplify_2 : simplify_spec 8468 6 468 6 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_res.
    reflexivity.
  - intros H_mod.
    reflexivity.
Qed.