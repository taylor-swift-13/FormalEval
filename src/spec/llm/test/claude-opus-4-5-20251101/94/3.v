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

Lemma is_prime_5107 : is_prime 5107.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d >= 2 /\ d <= 71) by lia.
    destruct H as [Hlo Hhi].
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/
            d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18 \/ d = 19 \/ d = 20 \/
            d = 21 \/ d = 22 \/ d = 23 \/ d = 24 \/ d = 25 \/ d = 26 \/ d = 27 \/ d = 28 \/ d = 29 \/ d = 30 \/
            d = 31 \/ d = 32 \/ d = 33 \/ d = 34 \/ d = 35 \/ d = 36 \/ d = 37 \/ d = 38 \/ d = 39 \/ d = 40 \/
            d = 41 \/ d = 42 \/ d = 43 \/ d = 44 \/ d = 45 \/ d = 46 \/ d = 47 \/ d = 48 \/ d = 49 \/ d = 50 \/
            d = 51 \/ d = 52 \/ d = 53 \/ d = 54 \/ d = 55 \/ d = 56 \/ d = 57 \/ d = 58 \/ d = 59 \/ d = 60 \/
            d = 61 \/ d = 62 \/ d = 63 \/ d = 64 \/ d = 65 \/ d = 66 \/ d = 67 \/ d = 68 \/ d = 69 \/ d = 70 \/
            d = 71) by lia.
    repeat (destruct H as [H|H]; [subst; compute; discriminate|]). subst; compute; discriminate.
Qed.

Lemma sum_of_digits_5107 : sum_of_digits 5107 = 13.
Proof.
  unfold sum_of_digits. simpl. reflexivity.
Qed.

Lemma in_5107 : In 5107 [1; 3; 1; 32; 5107; 34; 83278; 109; 163; 23; 2323; 32; 30; 1; 9; 3].
Proof.
  simpl. right. right. right. right. left. reflexivity.
Qed.

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

Lemma not_prime_32 : ~ is_prime 32.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 32) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma not_prime_34 : ~ is_prime 34.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 34) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma not_prime_83278 : ~ is_prime 83278.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 83278) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma not_prime_2323 : ~ is_prime 2323.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 23). 
  assert (2 <= 23) by lia.
  assert (23 * 23 <= 2323) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma not_prime_30 : ~ is_prime 30.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 30) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma not_prime_9 : ~ is_prime 9.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 3). 
  assert (2 <= 3) by lia.
  assert (3 * 3 <= 9) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma largest_prime_is_5107 : is_largest_prime 5107 [1; 3; 1; 32; 5107; 34; 83278; 109; 163; 23; 2323; 32; 30; 1; 9; 3].
Proof.
  unfold is_largest_prime. split.
  - exact in_5107.
  - split.
    + exact is_prime_5107.
    + intros y Hy Hprime.
      simpl in Hy.
      destruct Hy as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]].
      * subst. exfalso. apply not_prime_1. exact Hprime.
      * subst. lia.
      * subst. exfalso. apply not_prime_1. exact Hprime.
      * subst. exfalso. apply not_prime_32. exact Hprime.
      * subst. lia.
      * subst. exfalso. apply not_prime_34. exact Hprime.
      * subst. exfalso. apply not_prime_83278. exact Hprime.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. exfalso. apply not_prime_2323. exact Hprime.
      * subst. exfalso. apply not_prime_32. exact Hprime.
      * subst. exfalso. apply not_prime_30. exact Hprime.
      * subst. exfalso. apply not_prime_1. exact Hprime.
      * subst. exfalso. apply not_prime_9. exact Hprime.
      * destruct H as [H|H].
        -- subst. lia.
        -- contradiction.
Qed.

Example test_skjkasdkd : skjkasdkd_spec [1; 3; 1; 32; 5107; 34; 83278; 109; 163; 23; 2323; 32; 30; 1; 9; 3] 13.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 5107.
  split.
  - exact largest_prime_is_5107.
  - exact sum_of_digits_5107.
Qed.