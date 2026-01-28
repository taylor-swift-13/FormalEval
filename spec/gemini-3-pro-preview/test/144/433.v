Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["5597/25757775"; "8577/291"] -> x1=5597, x2=25757775, n1=8577, n2=291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 5597 25757775 8577 291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_res.
    inversion H_res.
  - intros H_mod.
    vm_compute in H_mod.
    discriminate.
Qed.