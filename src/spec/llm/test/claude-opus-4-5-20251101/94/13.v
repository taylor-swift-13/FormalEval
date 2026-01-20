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

Lemma is_prime_41 : is_prime 41.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
    destruct H as [H|[H|[H|[H|H]]]]; subst; compute; discriminate.
Qed.

Lemma sum_of_digits_41 : sum_of_digits 41 = 5.
Proof.
  unfold sum_of_digits. simpl. reflexivity.
Qed.

Lemma in_41 : In 41 [7; 9; 13; 17; 19; 23; 29; 31; 37; 41].
Proof.
  simpl. right. right. right. right. right. right. right. right. right. left. reflexivity.
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

Lemma is_prime_7 : is_prime 7.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2) by lia.
    subst; compute; discriminate.
Qed.

Lemma is_prime_13 : is_prime 13.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3) by lia.
    destruct H as [H|H]; subst; compute; discriminate.
Qed.

Lemma is_prime_17 : is_prime 17.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4) by lia.
    destruct H as [H|[H|H]]; subst; compute; discriminate.
Qed.

Lemma is_prime_19 : is_prime 19.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4) by lia.
    destruct H as [H|[H|H]]; subst; compute; discriminate.
Qed.

Lemma is_prime_23 : is_prime 23.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4) by lia.
    destruct H as [H|[H|H]]; subst; compute; discriminate.
Qed.

Lemma is_prime_29 : is_prime 29.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5) by lia.
    destruct H as [H|[H|[H|H]]]; subst; compute; discriminate.
Qed.

Lemma is_prime_31 : is_prime 31.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5) by lia.
    destruct H as [H|[H|[H|H]]]; subst; compute; discriminate.
Qed.

Lemma is_prime_37 : is_prime 37.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
    destruct H as [H|[H|[H|[H|H]]]]; subst; compute; discriminate.
Qed.

Lemma largest_prime_is_41 : is_largest_prime 41 [7; 9; 13; 17; 19; 23; 29; 31; 37; 41].
Proof.
  unfold is_largest_prime. split.
  - exact in_41.
  - split.
    + exact is_prime_41.
    + intros y Hy Hprime.
      simpl in Hy.
      destruct Hy as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
      * subst. lia.
      * subst. exfalso. apply not_prime_9. exact Hprime.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * destruct H as [H|H].
        -- subst. lia.
        -- contradiction.
Qed.

Example test_skjkasdkd : skjkasdkd_spec [7; 9; 13; 17; 19; 23; 29; 31; 37; 41] 5.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 41.
  split.
  - exact largest_prime_is_41.
  - exact sum_of_digits_41.
Qed.