Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["20/25"; "25/20"] -> x1=20, x2=25, n1=25, n2=20
   Output: true -> result=true
*)
Example test_simplify_1 : simplify_spec 20 25 25 20 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (20 * 25) mod (25 * 20) *)
    (* 20 * 25 = 500 *)
    (* 25 * 20 = 500 *)
    (* 500 mod 500 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.