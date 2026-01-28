Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

Example test_simplify_2 : simplify_spec 467 7736 9443 29 false.
Proof.
  unfold simplify_spec.
  intros _.
  split.
  - intros H.
    inversion H.
  - intros H.
    vm_compute in H.
    inversion H.
Qed.