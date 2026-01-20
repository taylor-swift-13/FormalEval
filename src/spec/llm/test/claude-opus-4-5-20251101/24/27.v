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

Example test_largest_divisor_75 : largest_divisor_spec 75 25.
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
           assert (Hd: d = 26 \/ d = 27 \/ d = 28 \/ d = 29 \/ d = 30 \/ 
                       d = 31 \/ d = 32 \/ d = 33 \/ d = 34 \/ d = 35 \/ 
                       d = 36 \/ d = 37 \/ d = 38 \/ d = 39 \/ d = 40 \/ 
                       d = 41 \/ d = 42 \/ d = 43 \/ d = 44 \/ d = 45 \/ 
                       d = 46 \/ d = 47 \/ d = 48 \/ d = 49 \/ d = 50 \/ 
                       d = 51 \/ d = 52 \/ d = 53 \/ d = 54 \/ d = 55 \/ 
                       d = 56 \/ d = 57 \/ d = 58 \/ d = 59 \/ d = 60 \/ 
                       d = 61 \/ d = 62 \/ d = 63 \/ d = 64 \/ d = 65 \/ 
                       d = 66 \/ d = 67 \/ d = 68 \/ d = 69 \/ d = 70 \/ 
                       d = 71 \/ d = 72 \/ d = 73 \/ d = 74) by lia.
           destruct Hd as [Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|
                          [Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|
                          [Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|
                          [Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|
                          [Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|[Hd|Hd]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
           subst d; compute; intro; discriminate.
Qed.