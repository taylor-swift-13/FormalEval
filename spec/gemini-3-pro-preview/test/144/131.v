Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/17"; "3/8"] -> x1=176, x2=17, n1=3, n2=8
   Output: false -> result=false
*)
Example test_simplify_new : simplify_spec 176 17 3 8 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* Here result is false, so false = true is a contradiction *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    (* Here we need to show that if mod = 0 then false = true *)
    (* We prove mod <> 0, so the premise is false *)
    intros H_mod.
    (* Compute values: 176 * 3 = 528, 17 * 8 = 136 *)
    (* 528 mod 136 = 120 <> 0 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.