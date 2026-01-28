Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["11/199"; "48468/66"] -> x1=11, x2=199, n1=48468, n2=66
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 11 199 48468 66 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> ... (contradiction) *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* 
       11 * 48468 = 533148
       199 * 66 = 13134
       533148 mod 13134 = 7788
       7788 <> 0, so H_mod is a contradiction 
    *)
    compute in H_mod.
    discriminate H_mod.
Qed.