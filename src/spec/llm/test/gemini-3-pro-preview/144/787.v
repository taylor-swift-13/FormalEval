Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["380/24"; "380/241"] -> x1=380, x2=24, n1=380, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 380 24 380 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> mod = 0 *)
    intros H_contra.
    discriminate H_contra.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Calculate the actual modulo value to show it is not 0 *)
    assert (H_calc : (380 * 380) mod (24 * 241) = 5584) by reflexivity.
    rewrite H_calc in H_mod.
    (* Now we have 5584 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.