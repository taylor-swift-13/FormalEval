Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/7"; "857/291"] -> x1=11, x2=7, n1=857, n2=291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 7 857 291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (11 * 857) mod (7 * 291) *)
    (* 11 * 857 = 9427 *)
    (* 7 * 291 = 2037 *)
    (* 9427 mod 2037 = 1279 *)
    (* 1279 <> 0, so H_mod is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.