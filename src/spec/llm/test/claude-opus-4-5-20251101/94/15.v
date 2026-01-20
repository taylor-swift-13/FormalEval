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

Lemma is_prime_449 : is_prime 449.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/ d = 16 \/ d = 17 \/ d = 18 \/ d = 19 \/ d = 20 \/ d = 21) by lia.
    destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]; subst; compute; discriminate.
Qed.

Lemma sum_of_digits_449 : sum_of_digits 449 = 17.
Proof.
  unfold sum_of_digits. simpl. reflexivity.
Qed.

Lemma in_449 : In 449 [181; 233; 293; 307; 331; 367; 379; 397; 433; 449].
Proof.
  simpl. right. right. right. right. right. right. right. right. right. left. reflexivity.
Qed.

Lemma largest_prime_is_449 : is_largest_prime 449 [181; 233; 293; 307; 331; 367; 379; 397; 433; 449].
Proof.
  unfold is_largest_prime. split.
  - exact in_449.
  - split.
    + exact is_prime_449.
    + intros y Hy Hprime.
      simpl in Hy.
      destruct Hy as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]].
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
      * contradiction.
Qed.

Example test_skjkasdkd : skjkasdkd_spec [181; 233; 293; 307; 331; 367; 379; 397; 433; 449] 17.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 449.
  split.
  - exact largest_prime_is_449.
  - exact sum_of_digits_449.
Qed.