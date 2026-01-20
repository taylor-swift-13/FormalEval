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

Lemma is_prime_29 : is_prime 29.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5) by lia.
    destruct H as [H|[H|[H|H]]]; subst; compute; discriminate.
Qed.

Lemma sum_of_digits_29 : sum_of_digits 29 = 11.
Proof.
  unfold sum_of_digits. simpl. reflexivity.
Qed.

Lemma in_29 : In 29 [0; 29; 2; 3; 5; 7; 11; 13; 17; 19; 23; 29].
Proof.
  simpl. right. left. reflexivity.
Qed.

Lemma not_prime_0 : ~ is_prime 0.
Proof. unfold is_prime. lia. Qed.

Lemma largest_prime_is_29 : is_largest_prime 29 [0; 29; 2; 3; 5; 7; 11; 13; 17; 19; 23; 29].
Proof.
  unfold is_largest_prime. split.
  - exact in_29.
  - split.
    + exact is_prime_29.
    + intros y Hy Hprime.
      simpl in Hy.
      destruct Hy as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]].
      * subst. exfalso. apply not_prime_0. exact Hprime.
      * subst. lia.
      * subst. lia.
      * subst. lia.
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

Example test_skjkasdkd : skjkasdkd_spec [0; 29; 2; 3; 5; 7; 11; 13; 17; 19; 23; 29] 11.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 29.
  split.
  - exact largest_prime_is_29.
  - exact sum_of_digits_29.
Qed.