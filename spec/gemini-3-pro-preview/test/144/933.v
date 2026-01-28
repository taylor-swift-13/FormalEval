Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["9493/29"; "9493/29"] -> x1=9493, x2=29, n1=9493, n2=29
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 9493 29 9493 29 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the values to show contradiction: 
       9493 * 9493 = 90117049
       29 * 29 = 841
       90117049 mod 841 = 535 <> 0 
    *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.