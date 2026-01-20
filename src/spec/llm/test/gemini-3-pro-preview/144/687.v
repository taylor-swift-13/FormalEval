Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8/113"; "23/5"] -> x1=8, x2=113, n1=23, n2=5
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 8 113 23 5 false.
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
    (* (8 * 23) mod (113 * 5) = 184 mod 565 = 184 *)
    (* 184 = 0 is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.