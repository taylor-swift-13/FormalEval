Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3/4"; "4/3"] -> x1=3, x2=4, n1=4, n2=3
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 3 4 4 3 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (3 * 4) mod (4 * 3) *)
    (* 3 * 4 = 12 *)
    (* 4 * 3 = 12 *)
    (* 12 mod 12 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.