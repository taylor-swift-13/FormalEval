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

Example test_largest_divisor_23: largest_divisor_spec 23 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - intros H. lia.
  - intros H. split.
    + lia.
    + split.
      * lia.
      * split.
        -- reflexivity.
        -- intros d H_gt H_lt.
           left.
           assert (H_cases: d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18 \/ d = 19 \/ d = 20 \/ d = 21 \/ d = 22) by lia.
           repeat destruct H_cases as [-> | H_cases]; try (intro C; compute in C; discriminate).
           subst. intro C; compute in C; discriminate.
Qed.