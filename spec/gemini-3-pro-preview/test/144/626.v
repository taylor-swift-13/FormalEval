Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1/10"; "100/10"] -> x1=1, x2=10, n1=100, n2=10
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 1 10 100 10 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (1 * 100) mod (10 * 10) *)
    (* 1 * 100 = 100 *)
    (* 10 * 10 = 100 *)
    (* 100 mod 100 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.