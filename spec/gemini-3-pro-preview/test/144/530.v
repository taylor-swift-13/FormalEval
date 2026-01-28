Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["357/55"; "357/55"] -> x1=357, x2=55, n1=357, n2=55
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 357 55 357 55 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (357 * 357) mod (55 * 55) evaluates to non-zero (399), so H_mod is False *)
    compute in H_mod.
    discriminate H_mod.
Qed.