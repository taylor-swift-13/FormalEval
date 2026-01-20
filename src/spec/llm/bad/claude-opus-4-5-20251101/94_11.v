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

Lemma is_prime_73 : is_prime 73.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8) by lia.
    destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; compute; try discriminate; lia.
Qed.

Lemma sum_of_digits_73 : sum_of_digits 73 = 10.
Proof.
  unfold sum_of_digits. simpl. reflexivity.
Qed.

Lemma in_73 : In 73 [10; 12; 73; 4; 6; 8; 10; 12].
Proof.
  simpl. right. right. left. reflexivity.
Qed.

Lemma not_prime_4 : ~ is_prime 4.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 4) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma not_prime_6 : ~ is_prime 6.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 6) by lia.
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

Lemma not_prime_10 : ~ is_prime 10.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 10) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma not_prime_12 : ~ is_prime 12.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 12) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma largest_prime_is_73 : is_largest_prime 73 [10; 12; 73; 4; 6; 8; 10; 12].
Proof.
  unfold is_largest_prime. split.
  - exact in_73.
  - split.
    + exact is_prime_73.
    + intros y Hy Hprime.
      simpl in Hy.
      destruct Hy as [H|[H|[H|[H|[H|[H|[H|[H|]]]]]]]].
      * subst. exfalso. apply not_prime_10. exact Hprime.
      * subst. exfalso. apply not_prime_12. exact Hprime.
      * subst. lia.
      * subst. exfalso. apply not_prime_4. exact Hprime.
      * subst. exfalso. apply not_prime_6. exact Hprime.
      * subst. exfalso. apply not_prime_8. exact Hprime.
      * subst. exfalso. apply not_prime_10. exact Hprime.
      * subst. exfalso. apply not_prime_12. exact Hprime.
Qed.

Example test_skjkasdkd : skjkasdkd_spec [10; 12; 73; 4; 6; 8; 10; 12] 10.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 73.
  split.
  - exact largest_prime_is_73.
  - exact sum_of_digits_73.
Qed.