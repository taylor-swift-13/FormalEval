Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2/10"; "50/10"] -> x1=2, x2=10, n1=50, n2=10
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 2 10 50 10 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (2 * 50) mod (10 * 10) *)
    (* 2 * 50 = 100 *)
    (* 10 * 10 = 100 *)
    (* 100 mod 100 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.