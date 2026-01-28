Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1119/1"; "4/3"] -> x1=1119, x2=1, n1=4, n2=3
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 1119 1 4 3 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (1119 * 4) mod (1 * 3) *)
    (* 1119 * 4 = 4476 *)
    (* 1 * 3 = 3 *)
    (* 4476 mod 3 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.