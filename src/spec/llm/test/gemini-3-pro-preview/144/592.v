Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3/8"; "33/8"] -> x1=3, x2=8, n1=33, n2=8
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 3 8 33 8 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (3 * 33) mod (8 * 8) *)
    (* 3 * 33 = 99 *)
    (* 8 * 8 = 64 *)
    (* 99 mod 64 = 35 *)
    (* 35 = 0 is false *)
    compute in H_mod.
    discriminate H_mod.
Qed.