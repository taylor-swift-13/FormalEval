Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["85777/291"; "943/2"] -> x1=85777, x2=291, n1=943, n2=2
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 85777 291 943 2 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    assert (H_calc : (85777 * 943) mod (291 * 2) <> 0).
    { vm_compute. intros H_eq. inversion H_eq. }
    rewrite H_mod in H_calc.
    contradiction.
Qed.