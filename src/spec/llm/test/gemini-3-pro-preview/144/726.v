Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2/252"; "138/113"] -> x1=2, x2=252, n1=138, n2=113
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 2 252 138 113 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* (2 * 138) mod (252 * 113) reduces to 276 mod 28476 = 276 *)
    compute in H_mod.
    discriminate H_mod.
Qed.