Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["616/6"; "6/1"] -> x1=616, x2=6, n1=6, n2=1
   Output: true -> result=true
*)
Example test_simplify_1 : simplify_spec 616 6 6 1 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Simplify algebraic expressions: (616 * 6) mod (6 * 1) *)
    (* 616 * 6 = 3696 *)
    (* 6 * 1 = 6 *)
    (* 3696 mod 6 = 0 *)
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.