Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["2/3"; "453/38"] -> x1=2, x2=3, n1=453, n2=38
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 2 3 453 38 false.
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