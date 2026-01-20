Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/17"; "467/7736"] -> x1=11, x2=17, n1=467, n2=7736
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 11 17 467 7736 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate modulo: (11 * 467) mod (17 * 7736) *)
    (* 11 * 467 = 5137 *)
    (* 17 * 7736 = 131512 *)
    (* 5137 mod 131512 = 5137 <> 0 *)
    compute in H_mod.
    discriminate H_mod.
Qed.