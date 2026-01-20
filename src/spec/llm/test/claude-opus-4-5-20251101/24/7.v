Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition largest_divisor_spec (n : Z) (result : Z) : Prop :=
  (n <= 1 -> result = 1) /\
  (n > 1 -> 
    result >= 1 /\
    result < n /\
    (n mod result = 0) /\
    (forall d : Z, d > result -> d < n -> n mod d <> 0 \/ d * (n / d) <> n / (n / d))).

Example test_largest_divisor_27 : largest_divisor_spec 27 9.
Proof.
  unfold largest_divisor_spec.
  split.
  - intro H. lia.
  - intro H.
    split.
    + lia.
    + split.
      * lia.
      * split.
        -- compute. reflexivity.
        -- intros d Hd1 Hd2.
           left.
           assert (Hd: d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18 \/ d = 19 \/ d = 20 \/ d = 21 \/ d = 22 \/ d = 23 \/ d = 24 \/ d = 25 \/ d = 26) by lia.
           destruct Hd as [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | [Hd | Hd]]]]]]]]]]]]]]]];
           subst d; compute; intro; discriminate.
Qed.