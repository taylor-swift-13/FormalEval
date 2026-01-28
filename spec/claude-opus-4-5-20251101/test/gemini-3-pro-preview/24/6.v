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

Example test_largest_divisor_2: largest_divisor_spec 2 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Case: n <= 1 *)
    intros H.
    lia.
  - (* Case: n > 1 *)
    intros H.
    split.
    + (* Prove result >= 1 *)
      lia.
    + split.
      * (* Prove result < n *)
        lia.
      * split.
        -- (* Prove n mod result = 0 *)
           reflexivity.
        -- (* Prove forall d, d > result -> d < n -> ... *)
           intros d H_gt H_lt.
           (* There is no integer d such that 1 < d < 2 *)
           lia.
Qed.