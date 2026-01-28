Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9/12"; "12/9"] -> x1=9, x2=12, n1=12, n2=9
   Output: true -> result=true
*)
Example test_simplify_1 : simplify_spec 9 12 12 9 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (9 * 12) mod (12 * 9) *)
    (* 9 * 12 = 108 *)
    (* 12 * 9 = 108 *)
    (* 108 mod 108 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.