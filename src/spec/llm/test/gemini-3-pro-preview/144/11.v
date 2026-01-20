Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2/4"; "4/2"] -> x1=2, x2=4, n1=4, n2=2
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 2 4 4 2 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (2 * 4) mod (4 * 2) *)
    (* 2 * 4 = 8 *)
    (* 4 * 2 = 8 *)
    (* 8 mod 8 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.