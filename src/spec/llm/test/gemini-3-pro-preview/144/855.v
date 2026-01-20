Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1/373"; "9291/739"] -> x1=1, x2=373, n1=9291, n2=739
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1 373 9291 739 false.
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
    (* Simplify algebraic expressions: (1 * 9291) mod (373 * 739) *)
    (* 1 * 9291 = 9291 *)
    (* 373 * 739 = 275647 *)
    (* 9291 mod 275647 = 9291 *)
    (* H_mod becomes 9291 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.