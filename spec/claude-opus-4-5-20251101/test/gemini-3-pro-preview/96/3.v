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

Example test_count_up_to_7: count_up_to_spec 7 [2; 3; 5].
Proof.
  unfold count_up_to_spec.
  split.
  - lia.
  - split.
    + intros x.
      split.
      * intros H_in.
        simpl in H_in.
        destruct H_in as [H2 | [H3 | [H5 | H_false]]].
        -- subst x.
           split.
           ++ unfold is_prime. split. lia.
              intros d H_min H_max. lia.
           ++ lia.
        -- subst x.
           split.
           ++ unfold is_prime. split. lia.
              intros d H_min H_max.
              assert (d = 2) by lia. subst d.
              intro H_div. compute in H_div. discriminate.
           ++ lia.
        -- subst x.
           split.
           ++ unfold is_prime. split. lia.
              intros d H_min H_max.
              assert (d = 2 \/ d = 3 \/ d = 4) as D by lia.
              destruct D as [D2 | [D3 | D4]]; subst d;
              intro H_div; compute in H_div; discriminate.
           ++ lia.
        -- contradiction.
      * intros [H_prime H_range].
        unfold is_prime in H_prime.
        destruct H_prime as [H_ge2 H_forall].
        assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6) as H_cases by lia.
        destruct H_cases as [H2 | [H3 | [H4 | [H5 | H6]]]].
        -- subst x. simpl. left. reflexivity.
        -- subst x. simpl. right. left. reflexivity.
        -- subst x.
           exfalso.
           apply (H_forall 2).
           ++ lia.
           ++ lia.
           ++ reflexivity.
        -- subst x. simpl. right. right. left. reflexivity.
        -- subst x.
           exfalso.
           apply (H_forall 2).
           ++ lia.
           ++ lia.
           ++ reflexivity.
    + intros i j H_lt H_bound.
      simpl in H_bound.
      assert ((i = 0 /\ j = 1) \/ (i = 0 /\ j = 2) \/ (i = 1 /\ j = 2)) as H_indices by lia.
      destruct H_indices as [[? ?] | [[? ?] | [? ?]]]; subst; simpl; lia.
Qed.