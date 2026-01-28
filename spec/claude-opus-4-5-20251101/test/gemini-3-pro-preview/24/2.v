Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  (n <= 1 -> result = 1) /\
  (n > 1 -> 
    result >= 1 /\
    result < n /\
    (n mod result = 0) /\
    (forall d : Z, d > result -> d < n -> n mod d <> 0 \/ d * (n / d) <> n / (n / d))).

Example test_largest_divisor_7: largest_divisor_spec 7 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - intros H.
    lia.
  - intros H.
    split.
    + lia.
    + split.
      * lia.
      * split.
        -- reflexivity.
        -- intros d H_gt H_lt.
           left.
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
           destruct H0 as [? | [? | [? | [? | ?]]]]; subst d; compute; discriminate.
Qed.