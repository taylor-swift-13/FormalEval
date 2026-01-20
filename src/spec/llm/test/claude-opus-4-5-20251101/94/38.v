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

Lemma is_prime_139 : is_prime 139.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10 \/ d = 11) by lia.
    destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]; subst; compute; discriminate.
Qed.

Lemma sum_of_digits_139 : sum_of_digits 139 = 13.
Proof.
  unfold sum_of_digits. simpl. reflexivity.
Qed.

Lemma in_139 : In 139 [3; 101; 103; 107; 109; 112; 127; 9; 131; 139].
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

Lemma not_prime_112 : ~ is_prime 112.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 112) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma largest_prime_is_139 : is_largest_prime 139 [3; 101; 103; 107; 109; 112; 127; 9; 131; 139].
Proof.
  unfold is_largest_prime. split.
  - exact in_139.
  - split.
    + exact is_prime_139.
    + intros y Hy Hprime.
      simpl in Hy.
      destruct Hy as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. exfalso. apply not_prime_112. exact Hprime.
      * subst. lia.
      * subst. exfalso. apply not_prime_9. exact Hprime.
      * subst. lia.
      * destruct H as [H|H].
        -- subst. lia.
        -- contradiction.
Qed.

Example test_skjkasdkd : skjkasdkd_spec [3; 101; 103; 107; 109; 112; 127; 9; 131; 139] 13.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 139.
  split.
  - exact largest_prime_is_139.
  - exact sum_of_digits_139.
Qed.