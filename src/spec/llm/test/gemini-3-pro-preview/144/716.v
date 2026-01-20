Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

Example test_simplify_new : simplify_spec 16311 9 467 736 false.
Proof.
  unfold simplify_spec.
  intros _.
  split.
  - intros H.
    discriminate.
  - intros H.
    vm_compute in H.
    discriminate.
Qed.