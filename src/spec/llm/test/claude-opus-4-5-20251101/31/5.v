Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_61 : is_prime_spec 61 true.
Proof.
  unfold is_prime_spec.
  split.
  - intro H. lia.
  - intro H.
    split.
    + intro Htrue.
      intros d Hd1 Hd2.
      assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d >= 8) by lia.
      destruct H0 as [H0 | [H0 | [H0 | [H0 | [H0 | [H0 | H0]]]]]].
      * subst d. compute. discriminate.
      * subst d. compute. discriminate.
      * subst d. compute. discriminate.
      * subst d. compute. discriminate.
      * subst d. compute. discriminate.
      * subst d. compute. discriminate.
      * assert (d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d >= 16) by lia.
        destruct H1 as [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]]].
        -- subst d. compute. discriminate.
        -- subst d. compute. discriminate.
        -- subst d. compute. discriminate.
        -- subst d. compute. discriminate.
        -- subst d. compute. discriminate.
        -- subst d. compute. discriminate.
        -- subst d. compute. discriminate.
        -- subst d. compute. discriminate.
        -- assert (d = 16 \/ d = 17 \/ d = 18 \/ d = 19 \/ d = 20 \/ d = 21 \/ d = 22 \/ d = 23 \/ d >= 24) by lia.
           destruct H2 as [H2 | [H2 | [H2 | [H2 | [H2 | [H2 | [H2 | [H2 | H2]]]]]]]].
           ++ subst d. compute. discriminate.
           ++ subst d. compute. discriminate.
           ++ subst d. compute. discriminate.
           ++ subst d. compute. discriminate.
           ++ subst d. compute. discriminate.
           ++ subst d. compute. discriminate.
           ++ subst d. compute. discriminate.
           ++ subst d. compute. discriminate.
           ++ assert (d = 24 \/ d = 25 \/ d = 26 \/ d = 27 \/ d = 28 \/ d = 29 \/ d = 30 \/ d >= 31) by lia.
              destruct H3 as [H3 | [H3 | [H3 | [H3 | [H3 | [H3 | [H3 | H3]]]]]]].
              ** subst d. compute. discriminate.
              ** subst d. compute. discriminate.
              ** subst d. compute. discriminate.
              ** subst d. compute. discriminate.
              ** subst d. compute. discriminate.
              ** subst d. compute. discriminate.
              ** subst d. compute. discriminate.
              ** assert (d = 31 \/ d = 32 \/ d = 33 \/ d = 34 \/ d = 35 \/ d = 36 \/ d = 37 \/ d = 38 \/ d = 39 \/ d = 40 \/ d = 41 \/ d = 42 \/ d = 43 \/ d = 44 \/ d = 45 \/ d = 46 \/ d = 47 \/ d = 48 \/ d = 49 \/ d = 50 \/ d = 51 \/ d = 52 \/ d = 53 \/ d = 54 \/ d = 55 \/ d = 56 \/ d = 57 \/ d = 58 \/ d = 59 \/ d = 60) by lia.
                 destruct H4 as [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | [H4 | H4]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; subst d; compute; discriminate.
    + intro Hdiv. reflexivity.
Qed.