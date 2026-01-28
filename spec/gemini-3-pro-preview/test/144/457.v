Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9999/01559557575"; "9999/01"] -> x1=9999, x2=1559557575, n1=9999, n2=1
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 9999 1559557575 9999 1 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_res.
    inversion H_res.
  - intros H_mod.
    vm_compute in H_mod.
    discriminate H_mod.
Qed.