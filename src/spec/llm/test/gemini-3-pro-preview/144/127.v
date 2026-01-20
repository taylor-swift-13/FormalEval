Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/25"; "7/25"] -> x1=7, x2=25, n1=7, n2=25
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 25 7 25 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (7 * 7) mod (25 * 25) *)
    (* 7 * 7 = 49 *)
    (* 25 * 25 = 625 *)
    (* 49 mod 625 = 49 *)
    compute in H_mod.
    (* H_mod becomes 49 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.