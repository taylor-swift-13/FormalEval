Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/255"; "453/84"] -> x1=7, x2=255, n1=453, n2=84
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 255 453 84 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (7 * 453) mod (255 * 84) *)
    (* 7 * 453 = 3171 *)
    (* 255 * 84 = 21420 *)
    (* 3171 mod 21420 = 3171 *)
    (* 3171 <> 0 *)
    compute in H_mod.
    discriminate H_mod.
Qed.