Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/71"; "16/17"] -> x1=23, x2=71, n1=16, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 71 16 17 false.
Proof.
  unfold simplify_spec.
  intros _.
  split.
  - intros H.
    discriminate H.
  - intros H.
    compute in H.
    discriminate H.
Qed.