Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/384"; "1613/58"] -> x1=453, x2=384, n1=1613, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 384 1613 58 false.
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