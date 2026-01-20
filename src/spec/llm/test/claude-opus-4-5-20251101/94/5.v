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

Lemma is_prime_3 : is_prime 3.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2) by lia.
    subst. compute. discriminate.
Qed.

Lemma sum_of_digits_3 : sum_of_digits 3 = 3.
Proof.
  unfold sum_of_digits. simpl. reflexivity.
Qed.

Lemma in_3 : In 3 [0; 81; 12; 3; 1; 21].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Lemma not_prime_0 : ~ is_prime 0.
Proof. unfold is_prime. lia. Qed.

Lemma not_prime_1 : ~ is_prime 1.
Proof. unfold is_prime. lia. Qed.

Lemma not_prime_81 : ~ is_prime 81.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 3). 
  assert (2 <= 3) by lia.
  assert (3 * 3 <= 81) by lia.
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

Lemma not_prime_21 : ~ is_prime 21.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 3). 
  assert (2 <= 3) by lia.
  assert (3 * 3 <= 21) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma largest_prime_is_3 : is_largest_prime 3 [0; 81; 12; 3; 1; 21].
Proof.
  unfold is_largest_prime. split.
  - exact in_3.
  - split.
    + exact is_prime_3.
    + intros y Hy Hprime.
      simpl in Hy.
      destruct Hy as [H|[H|[H|[H|[H|H]]]]].
      * subst. exfalso. apply not_prime_0. exact Hprime.
      * subst. exfalso. apply not_prime_81. exact Hprime.
      * subst. exfalso. apply not_prime_12. exact Hprime.
      * subst. lia.
      * subst. exfalso. apply not_prime_1. exact Hprime.
      * destruct H as [H|H].
        -- subst. exfalso. apply not_prime_21. exact Hprime.
        -- contradiction.
Qed.

Example test_skjkasdkd : skjkasdkd_spec [0; 81; 12; 3; 1; 21] 3.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 3.
  split.
  - exact largest_prime_is_3.
  - exact sum_of_digits_3.
Qed.