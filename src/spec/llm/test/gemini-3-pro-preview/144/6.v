Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/2"; "4/2"] -> x1=7, x2=2, n1=4, n2=2
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 7 2 4 2 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (7 * 4) mod (2 * 2) *)
    (* 7 * 4 = 28 *)
    (* 2 * 2 = 4 *)
    (* 28 mod 4 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.