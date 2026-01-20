Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["48468/6"; "9999/010"] -> x1=48468, x2=6, n1=9999, n2=10
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 48468 6 9999 10 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Verify that (48468 * 9999) mod (6 * 10) is not 0 *)
    vm_compute in H_mod.
    discriminate.
Qed.