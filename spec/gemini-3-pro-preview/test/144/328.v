Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/7"; "467/7736"] -> x1=11, x2=7, n1=467, n2=7736
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 7 467 7736 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (11 * 467) mod (7 * 7736) *)
    (* 11 * 467 = 5137 *)
    (* 7 * 7736 = 54152 *)
    (* 5137 mod 54152 = 5137 *)
    (* Hypothesis becomes 5137 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.