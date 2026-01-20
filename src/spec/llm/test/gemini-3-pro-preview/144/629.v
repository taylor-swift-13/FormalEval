Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["999999/1"; "1/999999"] -> x1=999999, x2=1, n1=1, n2=999999
   Output: true -> result=true
*)
Example test_simplify_1 : simplify_spec 999999 1 1 999999 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (999999 * 1) mod (1 * 999999) *)
    (* 999999 * 1 = 999999 *)
    (* 1 * 999999 = 999999 *)
    (* 999999 mod 999999 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.