Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8/1325"; "3/8"] -> x1=8, x2=1325, n1=3, n2=8
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 8 1325 3 8 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (8 * 3) mod (1325 * 8) *)
    (* 8 * 3 = 24 *)
    (* 1325 * 8 = 10600 *)
    (* 24 mod 10600 = 24 *)
    (* 24 = 0 is a contradiction *)
    compute in H_mod.
    discriminate.
Qed.