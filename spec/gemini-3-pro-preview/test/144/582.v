Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/2"; "9943/29"] -> x1=7, x2=2, n1=9943, n2=29
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 2 9943 29 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is contradictory *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (7 * 9943) mod (2 * 29) *)
    (* 7 * 9943 = 69601 *)
    (* 2 * 29 = 58 *)
    (* 69601 mod 58 = 1 *)
    (* H_mod becomes 1 = 0, which is contradictory *)
    compute in H_mod.
    discriminate H_mod.
Qed.