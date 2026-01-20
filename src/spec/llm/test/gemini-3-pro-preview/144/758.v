Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["597/275"; "8/113"] -> x1=597, x2=275, n1=8, n2=113
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 597 275 8 113 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (597 * 8) mod (275 * 113) *)
    (* 597 * 8 = 4776 *)
    (* 275 * 113 = 31075 *)
    (* 4776 mod 31075 = 4776 *)
    (* H_mod becomes 4776 = 0, which is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.