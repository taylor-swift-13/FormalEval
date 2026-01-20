Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["13/19"; "19/13"] -> x1=13, x2=19, n1=19, n2=13
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 13 19 19 13 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (13 * 19) mod (19 * 13) *)
    (* 13 * 19 = 247 *)
    (* 19 * 13 = 247 *)
    (* 247 mod 247 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.