Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["25/20"; "8/3"] -> x1=25, x2=20, n1=8, n2=3
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 25 20 8 3 false.
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
    (* Simplify algebraic expressions: (25 * 8) mod (20 * 3) *)
    (* 25 * 8 = 200 *)
    (* 20 * 3 = 60 *)
    (* 200 mod 60 = 20 *)
    (* H_mod : 20 = 0, which is contradictory *)
    compute in H_mod.
    discriminate H_mod.
Qed.