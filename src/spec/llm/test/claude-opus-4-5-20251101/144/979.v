Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_168553_658_8523_522291 : simplify_spec 168553 658 8523 522291 false.
Proof.
  unfold simplify_spec.
  split.
  - lia.
  - split.
    + lia.
    + split.
      * intros H. 
        compute in H.
        discriminate H.
      * intros H. discriminate H.
Qed.