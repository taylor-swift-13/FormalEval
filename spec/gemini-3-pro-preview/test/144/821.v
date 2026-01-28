Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["943/29"; "97176/9"] -> x1=943, x2=29, n1=97176, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 943 29 97176 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_res.
    inversion H_res.
  - intros H_mod.
    vm_compute in H_mod.
    discriminate H_mod.
Qed.