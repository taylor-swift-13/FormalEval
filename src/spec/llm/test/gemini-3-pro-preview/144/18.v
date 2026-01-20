Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["15/17"; "17/15"] -> x1=15, x2=17, n1=17, n2=15
   Output: true -> result=true
*)
Example test_simplify_1 : simplify_spec 15 17 17 15 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (15 * 17) mod (17 * 15) *)
    (* 15 * 17 = 255 *)
    (* 17 * 15 = 255 *)
    (* 255 mod 255 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.