Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["133/19"; "133/19"] -> x1=133, x2=19, n1=133, n2=19
   Output: true -> result=true
*)
Example test_simplify_2 : simplify_spec 133 19 133 19 true.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    reflexivity.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    reflexivity.
Qed.