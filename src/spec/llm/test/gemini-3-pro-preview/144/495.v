Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1111/7"; "11711/7"] -> x1=1111, x2=7, n1=11711, n2=7
   Output: true -> result=true
*)
Example test_simplify_1 : simplify_spec 1111 7 11711 7 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (1111 * 11711) mod (7 * 7) *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.