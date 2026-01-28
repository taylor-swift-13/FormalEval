Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/9"; "1111/7"] -> x1=11, x2=9, n1=1111, n2=7
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 9 1111 7 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (11 * 1111) mod (9 * 7) *)
    (* 11 * 1111 = 12221 *)
    (* 9 * 7 = 63 *)
    (* 12221 mod 63 = 62 *)
    (* Hypothesis H_mod becomes 62 = 0, which is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.