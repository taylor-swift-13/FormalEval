Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/739"; "99/100"] -> x1=921, x2=739, n1=99, n2=100
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 921 739 99 100 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_res.
    discriminate H_res.
  - intros H_mod.
    compute in H_mod.
    discriminate H_mod.
Qed.