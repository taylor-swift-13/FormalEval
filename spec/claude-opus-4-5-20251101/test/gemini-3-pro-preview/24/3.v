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

Example test_largest_divisor_10: largest_divisor_spec 10 5.
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
        -- (* Prove n mod result = 0, i.e., 10 mod 5 = 0 *)
           reflexivity.
        -- (* Prove forall d, d > result -> d < n -> ... *)
           intros d H_gt H_lt.
           (* d must be 6, 7, 8, or 9 *)
           assert (d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia.
           destruct H0 as [H0 | [H0 | [H0 | H0]]]; subst d; left; intro H_contra; compute in H_contra; discriminate H_contra.
Qed.