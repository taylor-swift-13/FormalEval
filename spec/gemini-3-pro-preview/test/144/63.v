Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["20/25"; "112/9"] -> x1=20, x2=25, n1=112, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 20 25 112 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (20 * 112) mod (25 * 9) *)
    (* 20 * 112 = 2240 *)
    (* 25 * 9 = 225 *)
    (* 2240 mod 225 = 215 *)
    (* H_mod becomes 215 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.