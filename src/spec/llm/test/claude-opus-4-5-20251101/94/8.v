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

Lemma is_prime_8191 : is_prime 8191.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d >= 2 /\ d <= 90) by lia.
    destruct (Z.eq_dec (8191 mod d) 0) as [Heq|Hneq].
    + exfalso.
      assert (Hrange: 2 <= d <= 90) by lia.
      destruct (Z.eq_dec d 2) as [->|Hn2]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 3) as [->|Hn3]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 4) as [->|Hn4]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 5) as [->|Hn5]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 6) as [->|Hn6]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 7) as [->|Hn7]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 8) as [->|Hn8]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 9) as [->|Hn9]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 10) as [->|Hn10]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 11) as [->|Hn11]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 12) as [->|Hn12]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 13) as [->|Hn13]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 14) as [->|Hn14]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 15) as [->|Hn15]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 16) as [->|Hn16]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 17) as [->|Hn17]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 18) as [->|Hn18]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 19) as [->|Hn19]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 20) as [->|Hn20]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 21) as [->|Hn21]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 22) as [->|Hn22]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 23) as [->|Hn23]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 24) as [->|Hn24]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 25) as [->|Hn25]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 26) as [->|Hn26]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 27) as [->|Hn27]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 28) as [->|Hn28]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 29) as [->|Hn29]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 30) as [->|Hn30]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 31) as [->|Hn31]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 32) as [->|Hn32]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 33) as [->|Hn33]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 34) as [->|Hn34]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 35) as [->|Hn35]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 36) as [->|Hn36]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 37) as [->|Hn37]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 38) as [->|Hn38]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 39) as [->|Hn39]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 40) as [->|Hn40]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 41) as [->|Hn41]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 42) as [->|Hn42]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 43) as [->|Hn43]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 44) as [->|Hn44]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 45) as [->|Hn45]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 46) as [->|Hn46]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 47) as [->|Hn47]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 48) as [->|Hn48]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 49) as [->|Hn49]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 50) as [->|Hn50]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 51) as [->|Hn51]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 52) as [->|Hn52]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 53) as [->|Hn53]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 54) as [->|Hn54]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 55) as [->|Hn55]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 56) as [->|Hn56]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 57) as [->|Hn57]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 58) as [->|Hn58]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 59) as [->|Hn59]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 60) as [->|Hn60]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 61) as [->|Hn61]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 62) as [->|Hn62]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 63) as [->|Hn63]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 64) as [->|Hn64]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 65) as [->|Hn65]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 66) as [->|Hn66]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 67) as [->|Hn67]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 68) as [->|Hn68]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 69) as [->|Hn69]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 70) as [->|Hn70]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 71) as [->|Hn71]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 72) as [->|Hn72]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 73) as [->|Hn73]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 74) as [->|Hn74]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 75) as [->|Hn75]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 76) as [->|Hn76]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 77) as [->|Hn77]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 78) as [->|Hn78]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 79) as [->|Hn79]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 80) as [->|Hn80]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 81) as [->|Hn81]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 82) as [->|Hn82]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 83) as [->|Hn83]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 84) as [->|Hn84]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 85) as [->|Hn85]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 86) as [->|Hn86]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 87) as [->|Hn87]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 88) as [->|Hn88]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 89) as [->|Hn89]. { compute in Heq. discriminate. }
      destruct (Z.eq_dec d 90) as [->|Hn90]. { compute in Heq. discriminate. }
      lia.
    + exact Hneq.
Qed.

Lemma sum_of_digits_8191 : sum_of_digits 8191 = 19.
Proof.
  unfold sum_of_digits. simpl. reflexivity.
Qed.

Lemma in_8191 : In 8191 [8191; 123456; 127; 7].
Proof.
  simpl. left. reflexivity.
Qed.

Lemma not_prime_123456 : ~ is_prime 123456.
Proof. 
  unfold is_prime. intros [H1 H2].
  specialize (H2 2). 
  assert (2 <= 2) by lia.
  assert (2 * 2 <= 123456) by lia.
  specialize (H2 H H0).
  compute in H2. congruence.
Qed.

Lemma largest_prime_is_8191 : is_largest_prime 8191 [8191; 123456; 127; 7].
Proof.
  unfold is_largest_prime. split.
  - exact in_8191.
  - split.
    + exact is_prime_8191.
    + intros y Hy Hprime.
      simpl in Hy.
      destruct Hy as [H|[H|[H|[H|H]]]].
      * subst. lia.
      * subst. exfalso. apply not_prime_123456. exact Hprime.
      * subst. lia.
      * subst. lia.
      * contradiction.
Qed.

Example test_skjkasdkd : skjkasdkd_spec [8191; 123456; 127; 7] 19.
Proof.
  unfold skjkasdkd_spec.
  left.
  exists 8191.
  split.
  - exact largest_prime_is_8191.
  - exact sum_of_digits_8191.
Qed.