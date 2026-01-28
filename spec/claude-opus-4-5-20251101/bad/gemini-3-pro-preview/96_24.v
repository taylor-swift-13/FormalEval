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

Example test_count_up_to_13: count_up_to_spec 13 [2; 3; 5; 7; 11].
Proof.
  unfold count_up_to_spec.
  split.
  - lia.
  - split.
    + intros x. split.
      * intros H_in.
        simpl in H_in.
        destruct H_in as [H | [H | [H | [H | [H | H]]]]]; subst x; split; try lia.
        -- unfold is_prime. split. lia. intros d H1 H2. lia.
        -- unfold is_prime. split. lia. intros d H1 H2. assert (d = 2) by lia. subst. simpl. discriminate.
        -- unfold is_prime. split. lia. intros d H1 H2. assert (d = 2 \/ d = 3 \/ d = 4) by lia. destruct H0; subst; simpl; discriminate.
        -- unfold is_prime. split. lia. intros d H1 H2. assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia. destruct H0 as [?|[?|[?|[?|?]]]]; subst; simpl; discriminate.
        -- unfold is_prime. split. lia. intros d H1 H2. assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10) by lia. destruct H0 as [?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]; subst; simpl; discriminate.
        -- contradiction.
      * intros [H_prime H_range].
        unfold is_prime in H_prime. destruct H_prime as [H_ge2 H_forall].
        assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12) as H_cases by lia.
        destruct H_cases as [?|[?|[?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]]]; subst x; simpl; auto.
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- exfalso. apply (H_forall 3); [lia|lia|reflexivity].
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
    + intros i j H_lt H_bound.
      simpl in H_bound.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) as Hi by lia.
      assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) as Hj by lia.
      destruct Hi as [?|[?|[?|[?|?]]]]; destruct Hj as [?|[?|[?|[?|?]]]]; subst; simpl; try lia.
Qed.