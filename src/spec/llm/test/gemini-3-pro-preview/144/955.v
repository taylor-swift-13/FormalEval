Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["72/25"; "7/25"] -> x1=72, x2=25, n1=7, n2=25
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 72 25 7 25 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res : false = true, which is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (72 * 7) mod (25 * 25) *)
    (* 72 * 7 = 504 *)
    (* 25 * 25 = 625 *)
    (* 504 mod 625 = 504 *)
    (* H_mod implies 504 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.