Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["468/13"; "468/13"] -> x1=468, x2=13, n1=468, n2=13
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 468 13 468 13 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (468 * 468) mod (13 * 13) *)
    (* 468 * 468 = 219024 *)
    (* 13 * 13 = 169 *)
    (* 219024 mod 169 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.