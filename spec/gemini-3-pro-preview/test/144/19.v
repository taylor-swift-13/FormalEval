Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8/11"; "11/8"] -> x1=8, x2=11, n1=11, n2=8
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 8 11 11 8 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (8 * 11) mod (11 * 8) *)
    (* 8 * 11 = 88 *)
    (* 11 * 8 = 88 *)
    (* 88 mod 88 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.