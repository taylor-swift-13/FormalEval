Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["911/9"; "911/9"] -> x1=911, x2=9, n1=911, n2=9
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 911 9 911 9 false.
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