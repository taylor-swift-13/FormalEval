Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (n : Z) : Prop :=
  n >= 2 /\ forall d : Z, 2 <= d -> d * d <= n -> n mod d <> 0.

Definition sum_of_digits (n : Z) : Z :=
  let fix aux (m : Z) (acc : Z) (fuel : nat) :=
    match fuel with
    | O => acc
    | S fuel' =>
      if m <=? 0 then acc
      else aux (m / 10) (acc + (m mod 10)) fuel'
    end
  in aux n 0 100%nat.

Definition is_largest_prime (x : Z) (lst : list Z) : Prop :=
  In x lst /\ is_prime x /\ forall y : Z, In y lst -> is_prime y -> y <= x.

Definition skjkasdkd_spec (lst : list Z) (result : Z) : Prop :=
  (exists x : Z, is_largest_prime x lst /\ result = sum_of_digits x) \/
  ((forall x : Z, In x lst -> ~ is_prime x) /\ result = 0).

Lemma is_prime_4597 : is_prime 4597.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ 
            d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18 \/ 
            d = 19 \/ d = 20 \/ d = 21 \/ d = 22 \/ d = 23 \/ d = 24 \/ d = 25 \/ d = 26 \/ 
            d = 27 \/ d = 28 \/ d = 29 \/ d = 30 \/ d = 31 \/ d = 32 \/ d = 33 \/ d = 34 \/ 
            d = 35 \/ d = 36 \/ d = 37 \/ d = 38 \/ d = 39 \/ d = 40 \/ d = 41 \/ d = 42 \/ 
            d = 43 \/ d = 44 \/ d = 45 \/ d = 46 \/ d = 47 \/ d = 48 \/ d = 49 \/ d = 50 \/ 
            d = 51 \/ d = 52 \/ d = 53 \/ d = 54 \/ d = 55 \/ d = 56 \/ d = 57 \/ d = 58 \/ 
            d = 59 \/ d = 60 \/ d = 61 \/ d = 62 \/ d = 63 \/ d = 64 \/ d = 65 \/ d = 66 \/ 
            d = 67) by lia.
    repeat (destruct H as [H|H]; [subst; compute; discriminate | ]); subst; compute; discriminate.
Qed.

Lemma sum_of_digits_4597 : sum_of_digits 4597 = 25.
Proof.
  unfold sum_of_digits. simpl. reflexivity.
Qed.

Lemma in_4597 : In 4597 [1; 0; 1; 8; 2; 4597; 2; 1; 3; 40; 1; 2; 1; 2; 4; 2; 5; 1].
Proof.
  simpl. right. right. right. right. right. left. reflexivity.
Qed.

Lemma not_prime_0 : ~ is_prime 0.
Proof. unfold is_prime. lia. Qed.

Lemma not_prime_1 : ~ is_prime 1.
Proof. unfold is_prime. lia. Qed.

Lemma not_prime_4 : ~ is_prime 4.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 4) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma not_prime_8 : ~ is_prime 8.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 8) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma not_prime_40 : ~ is_prime 40.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 40) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma largest_prime_is_4597 : is_largest_prime 4597 [1; 0; 1; 8; 2; 4597; 2; 1; 3; 40; 1; 2; 1; 2; 4; 2; 5; 1].
Proof.
  unfold is_largest_prime. split.
  - exact in_4597.
  - split.
    + exact is_prime_4597.
    + intros y Hy Hprime.
      simpl in Hy.
      destruct Hy as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]].
      * subst. exfalso. apply not_prime_1. exact Hprime.
      * subst. exfalso. apply not_prime_0. exact Hprime.
      * subst. exfalso. apply not_prime_1. exact Hprime.
      * subst. exfalso. apply not_prime_8. exact Hprime.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. exfalso. apply not_prime_1. exact Hprime.
      * subst. lia.
      * subst. exfalso. apply not_prime_40. exact Hprime.
      * subst. exfalso. apply not_prime_1. exact Hprime.
      * subst. lia.
      * subst. exfalso. apply not_prime_1. exact Hprime.
      * subst. lia.
      * subst. exfalso. apply not_prime_4. exact Hprime.
      * subst. lia.
      * subst. lia.
      * destruct H as [H|H].
        -- subst. exfalso. apply not_prime_1. exact Hprime.
        -- contradiction.
Qed.

Example test_skjkasdkd : skjkasdkd_spec [1; 0; 1; 8; 2; 4597; 2; 1; 3; 40; 1; 2; 1; 2; 4; 2; 5; 1] 25.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 4597.
  split.
  - exact largest_prime_is_4597.
  - exact sum_of_digits_4597.
Qed.