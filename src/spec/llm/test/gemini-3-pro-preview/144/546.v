Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/669"; "467/7736"] -> x1=176, x2=669, n1=467, n2=7736
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 176 669 467 7736 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (176 * 467) mod (669 * 7736) *)
    (* 176 * 467 = 82192 *)
    (* 669 * 7736 = 5175384 *)
    (* 82192 mod 5175384 = 82192 *)
    (* 82192 = 0 is false *)
    compute in H_mod.
    discriminate.
Qed.