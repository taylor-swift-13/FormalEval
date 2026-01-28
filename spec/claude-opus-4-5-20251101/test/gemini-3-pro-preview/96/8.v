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

Example test_count_up_to_18: count_up_to_spec 18 [2; 3; 5; 7; 11; 13; 17].
Proof.
  unfold count_up_to_spec.
  split.
  - (* n >= 0 *)
    lia.
  - split.
    + (* Membership property *)
      intros x.
      split.
      * (* Forward: In x [2..17] -> is_prime x /\ 2 <= x < 18 *)
        intros H_in.
        simpl in H_in.
        destruct H_in as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; [..|contradiction]; subst x; split; try lia.
        -- (* 2 *)
           unfold is_prime. split; [lia|]. intros d H1 H2. lia.
        -- (* 3 *)
           unfold is_prime. split; [lia|]. intros d H1 H2. 
           assert (d = 2) by lia. subst. intro C. compute in C. discriminate.
        -- (* 5 *)
           unfold is_prime. split; [lia|]. intros d H1 H2.
           assert (d = 2 \/ d = 3 \/ d = 4) by lia.
           destruct H as [?|[?|?]]; subst; intro C; compute in C; discriminate.
        -- (* 7 *)
           unfold is_prime. split; [lia|]. intros d H1 H2.
           assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
           repeat destruct H as [H|H]; subst; intro C; compute in C; discriminate.
        -- (* 11 *)
           unfold is_prime. split; [lia|]. intros d H1 H2.
           assert (d=2\/d=3\/d=4\/d=5\/d=6\/d=7\/d=8\/d=9\/d=10) by lia.
           repeat destruct H as [H|H]; subst; intro C; compute in C; discriminate.
        -- (* 13 *)
           unfold is_prime. split; [lia|]. intros d H1 H2.
           assert (d=2\/d=3\/d=4\/d=5\/d=6\/d=7\/d=8\/d=9\/d=10\/d=11\/d=12) by lia.
           repeat destruct H as [H|H]; subst; intro C; compute in C; discriminate.
        -- (* 17 *)
           unfold is_prime. split; [lia|]. intros d H1 H2.
           assert (d=2\/d=3\/d=4\/d=5\/d=6\/d=7\/d=8\/d=9\/d=10\/d=11\/d=12\/d=13\/d=14\/d=15\/d=16) by lia.
           repeat destruct H as [H|H]; subst; intro C; compute in C; discriminate.
      * (* Backward: is_prime x /\ 2 <= x < 18 -> In x [...] *)
        intros [H_prime H_range].
        unfold is_prime in H_prime. destruct H_prime as [H_ge2 H_forall].
        assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/ x = 16 \/ x = 17) by lia.
        destruct H as [?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]]]]]]]]; subst x.
        -- simpl. left. reflexivity.
        -- simpl. right. left. reflexivity.
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- simpl. auto 10.
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- simpl. auto 10.
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- exfalso. apply (H_forall 3); [lia|lia|reflexivity].
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- simpl. auto 10.
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- simpl. auto 10.
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- exfalso. apply (H_forall 3); [lia|lia|reflexivity].
        -- exfalso. apply (H_forall 2); [lia|lia|reflexivity].
        -- simpl. auto 10.
    + (* Sorted property *)
      intros i j H_lt H_bound.
      simpl in H_bound.
      assert (0 <= i < 7) by lia.
      assert (0 <= j < 7) by lia.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
      destruct H1 as [?|[?|[?|[?|[?|[?|?]]]]]]; subst i;
      assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6) by lia;
      destruct H1 as [?|[?|[?|[?|[?|[?|?]]]]]]; subst j;
      try lia; simpl; lia.
Qed.