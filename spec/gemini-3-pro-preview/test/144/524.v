Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/3384"; "453/384"] -> x1=453, x2=3384, n1=453, n2=384
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 3384 453 384 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* Here result is false, so false = true is a contradiction *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (453 * 453) mod (3384 * 384) *)
    (* 453 * 453 = 205209 *)
    (* 3384 * 384 = 1299456 *)
    (* 205209 mod 1299456 = 205209 *)
    (* H_mod becomes 205209 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.