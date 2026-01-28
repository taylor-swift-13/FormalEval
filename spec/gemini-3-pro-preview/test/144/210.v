Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/669"; "8/13"] -> x1=176, x2=669, n1=8, n2=13
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 176 669 8 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (176 * 8) mod (669 * 13) *)
    (* 176 * 8 = 1408 *)
    (* 669 * 13 = 8697 *)
    (* 1408 mod 8697 = 1408 *)
    (* H_mod becomes 1408 = 0, which is impossible *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.