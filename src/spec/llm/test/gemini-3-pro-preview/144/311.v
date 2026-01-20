Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3080/241"; "7/255"] -> x1=3080, x2=241, n1=7, n2=255
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 3080 241 7 255 false.
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
    (* Simplify algebraic expressions: (3080 * 7) mod (241 * 255) *)
    (* 3080 * 7 = 21560 *)
    (* 241 * 255 = 61455 *)
    (* 21560 mod 61455 = 21560 *)
    (* 21560 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.