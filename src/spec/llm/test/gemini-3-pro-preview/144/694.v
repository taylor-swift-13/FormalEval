Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["711/7"; "380/241"] -> x1=711, x2=7, n1=380, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 711 7 380 241 false.
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