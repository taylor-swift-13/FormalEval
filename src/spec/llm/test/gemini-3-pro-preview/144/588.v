Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["467/77636"; "48468/66"] -> x1=467, x2=77636, n1=48468, n2=66
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 467 77636 48468 66 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the actual modulo value to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to a contradiction (non-zero value = 0) *)
    discriminate H_mod.
Qed.