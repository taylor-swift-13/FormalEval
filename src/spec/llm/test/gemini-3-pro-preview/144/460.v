Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["43/384"; "9999/0100"] -> x1=43, x2=384, n1=9999, n2=100
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 43 384 9999 100 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_res.
    inversion H_res.
  - intros H_mod.
    compute in H_mod.
    discriminate H_mod.
Qed.