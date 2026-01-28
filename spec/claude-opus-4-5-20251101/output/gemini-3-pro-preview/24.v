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

Example test_largest_divisor_3: largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Case: n <= 1 *)
    intros H.
    (* 3 <= 1 is false, so the implication holds trivially *)
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
        -- (* Prove n mod result = 0, i.e., 3 mod 1 = 0 *)
           reflexivity.
        -- (* Prove forall d, d > result -> d < n -> ... *)
           intros d H_gt H_lt.
           (* Since d is an integer and 1 < d < 3, d must be 2 *)
           assert (d = 2) by lia.
           subst d.
           (* We choose the left side of the disjunction: 3 mod 2 <> 0 *)
           left.
           intro H_contra.
           (* 3 mod 2 evaluates to 1, and 1 = 0 is a contradiction *)
           compute in H_contra.
           discriminate H_contra.
Qed.