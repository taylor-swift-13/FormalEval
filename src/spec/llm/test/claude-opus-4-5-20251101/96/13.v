Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p >= 2 /\
  forall d : Z, 2 <= d -> d < p -> ~(p mod d = 0).

Definition count_up_to_spec (n : Z) (result : list Z) : Prop :=
  n >= 0 /\
  (forall x, In x result <-> (is_prime x /\ 2 <= x < n)) /\
  (forall i j, 0 <= i < j -> j < Z.of_nat (length result) ->
    nth (Z.to_nat i) result 0 < nth (Z.to_nat j) result 0).

Lemma is_prime_2 : is_prime 2.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2. lia.
Qed.

Lemma is_prime_3 : is_prime 3.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2) by lia.
    subst. intro H. discriminate.
Qed.

Lemma is_prime_5 : is_prime 5.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4) as Hcases by lia.
    destruct Hcases as [H | [H | H]]; subst; intro Hmod; discriminate.
Qed.

Lemma is_prime_7 : is_prime 7.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) as Hcases by lia.
    destruct Hcases as [H | [H | [H | [H | H]]]]; subst; intro Hmod; discriminate.
Qed.

Lemma is_prime_11 : is_prime 11.
Proof.
  unfold is_prime. split.
  - lia.
  - intros d Hd1 Hd2.
    assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10) as Hcases by lia.
    destruct Hcases as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]; subst; intro Hmod; discriminate.
Qed.

Lemma not_prime_4 : ~is_prime 4.
Proof.
  unfold is_prime. intros [_ H].
  specialize (H 2 ltac:(lia) ltac:(lia)).
  apply H. reflexivity.
Qed.

Lemma not_prime_6 : ~is_prime 6.
Proof.
  unfold is_prime. intros [_ H].
  specialize (H 2 ltac:(lia) ltac:(lia)).
  apply H. reflexivity.
Qed.

Lemma not_prime_8 : ~is_prime 8.
Proof.
  unfold is_prime. intros [_ H].
  specialize (H 2 ltac:(lia) ltac:(lia)).
  apply H. reflexivity.
Qed.

Lemma not_prime_9 : ~is_prime 9.
Proof.
  unfold is_prime. intros [_ H].
  specialize (H 3 ltac:(lia) ltac:(lia)).
  apply H. reflexivity.
Qed.

Lemma not_prime_10 : ~is_prime 10.
Proof.
  unfold is_prime. intros [_ H].
  specialize (H 2 ltac:(lia) ltac:(lia)).
  apply H. reflexivity.
Qed.

Example count_up_to_test : count_up_to_spec 12 [2; 3; 5; 7; 11].
Proof.
  unfold count_up_to_spec.
  split.
  - lia.
  - split.
    + intros x. split.
      * intros Hin.
        simpl in Hin.
        destruct Hin as [H | [H | [H | [H | [H | H]]]]].
        -- subst x. split. apply is_prime_2. lia.
        -- subst x. split. apply is_prime_3. lia.
        -- subst x. split. apply is_prime_5. lia.
        -- subst x. split. apply is_prime_7. lia.
        -- subst x. split. apply is_prime_11. lia.
        -- contradiction.
      * intros [[Hge Hdiv] Hrange].
        simpl.
        assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x >= 12) as Hcases by lia.
        destruct Hcases as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]].
        -- left. symmetry. exact H.
        -- right. left. symmetry. exact H.
        -- subst x. exfalso. apply not_prime_4. split; assumption.
        -- right. right. left. symmetry. exact H.
        -- subst x. exfalso. apply not_prime_6. split; assumption.
        -- right. right. right. left. symmetry. exact H.
        -- subst x. exfalso. apply not_prime_8. split; assumption.
        -- subst x. exfalso. apply not_prime_9. split; assumption.
        -- subst x. exfalso. apply not_prime_10. split; assumption.
        -- right. right. right. right. left. symmetry. exact H.
        -- lia.
    + intros i j Hij Hj.
      simpl in Hj.
      simpl.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as Hi by lia.
      assert (j = 1 \/ j = 2 \/ j = 3 \/ j = 4) as Hj' by lia.
      destruct Hi as [Hi | [Hi | [Hi | Hi]]]; destruct Hj' as [Hj'' | [Hj'' | [Hj'' | Hj'']]]; subst; try lia; simpl; lia.
Qed.