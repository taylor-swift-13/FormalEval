Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["597/275"; "7/25"] -> x1=597, x2=275, n1=7, n2=25
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 597 275 7 25 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (597 * 7) mod (275 * 25) *)
    (* 597 * 7 = 4179 *)
    (* 275 * 25 = 6875 *)
    (* 4179 mod 6875 = 4179 *)
    (* 4179 = 0 is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.