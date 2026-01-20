Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["5597/2755775"; "5597/2755775"] -> x1=5597, x2=2755775, n1=5597, n2=2755775
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 5597 2755775 5597 2755775 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    vm_compute in H_mod.
    discriminate H_mod.
Qed.