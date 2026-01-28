Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["716/17"; "16/17"] -> x1=716, x2=17, n1=16, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 716 17 16 17 false.
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