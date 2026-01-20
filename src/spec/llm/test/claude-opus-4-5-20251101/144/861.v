Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_31683_5841_163_58 : simplify_spec 31683 5841 163 58 false.
Proof.
  unfold simplify_spec.
  split.
  - lia.
  - split.
    + lia.
    + split.
      * intros H. compute in H. discriminate.
      * intros H. discriminate.
Qed.