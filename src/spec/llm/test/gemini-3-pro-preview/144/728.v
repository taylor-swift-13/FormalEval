Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9176/9"; "11/7"] -> x1=9176, x2=9, n1=11, n2=7
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9176 9 11 7 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    compute in H_mod.
    discriminate.
Qed.