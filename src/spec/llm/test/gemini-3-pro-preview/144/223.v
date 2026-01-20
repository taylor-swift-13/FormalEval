Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["111/7"; "1111/7"] -> x1=111, x2=7, n1=1111, n2=7
   Output: false -> result=false
*)
Example test_simplify_new : simplify_spec 111 7 1111 7 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> ... *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* (111 * 1111) mod (7 * 7) evaluates to 37 *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.