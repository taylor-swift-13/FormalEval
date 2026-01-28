Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3/119"; "13/19"] -> x1=3, x2=119, n1=13, n2=19
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3 119 13 19 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (3 * 13) mod (119 * 19) *)
    (* 3 * 13 = 39 *)
    (* 119 * 19 = 2261 *)
    (* 39 mod 2261 = 39 *)
    (* 39 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.