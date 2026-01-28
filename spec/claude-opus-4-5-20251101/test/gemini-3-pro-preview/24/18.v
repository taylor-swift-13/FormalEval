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

Example test_largest_divisor_73: largest_divisor_spec 73 1.
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
           intro H_contra.
           assert (H_range: 2 <= d /\ d <= 72) by lia.
           repeat match goal with
           | [ H : 2 <= d /\ d <= ?u |- _ ] =>
             let is_small := eval compute in (Z.ltb u 2) in
             match is_small with
             | true => fail 1
             | false =>
                 let u_prev := eval compute in (u - 1) in
                 destruct (Z.eq_dec d u);
                 [ subst d; compute in H_contra; discriminate H_contra
                 | assert (H_new: 2 <= d /\ d <= u_prev) by lia;
                   clear H; rename H_new into H ]
             end
           end.
           lia.
Qed.