Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["467/7636"; "176/669"] -> x1=467, x2=7636, n1=176, n2=669
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 467 7636 176 669 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_res.
    discriminate.
  - intros H_mod.
    vm_compute in H_mod.
    discriminate.
Qed.