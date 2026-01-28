Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["85388/13131"; "9211/7"] -> x1=85388, x2=13131, n1=9211, n2=7
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 85388 13131 9211 7 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Verify that mod is not 0 *)
    vm_compute in H_mod.
    discriminate.
Qed.