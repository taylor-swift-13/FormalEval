Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["15/117"; "15/117"] -> x1=15, x2=117, n1=15, n2=117
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 15 117 15 117 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (15 * 15) mod (117 * 117) evaluates to 225 *)
    (* 225 = 0 is impossible *)
    compute in H_mod.
    discriminate H_mod.
Qed.