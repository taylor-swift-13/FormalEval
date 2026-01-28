Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8/3"; "33/2"] -> x1=8, x2=3, n1=33, n2=2
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 8 3 33 2 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (8 * 33) mod (3 * 2) *)
    (* 8 * 33 = 264 *)
    (* 3 * 2 = 6 *)
    (* 264 mod 6 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.