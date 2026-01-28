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

Example test_count_up_to_17: count_up_to_spec 17 [2; 3; 5; 7; 11; 13].
Proof.
  unfold count_up_to_spec.
  split.
  - (* n >= 0 *)
    lia.
  - split.
    + (* Membership property *)
      intros x.
      split.
      * (* Forward: In list -> prime /\ range *)
        intros H_in.
        simpl in H_in.
        destruct H_in as [H2 | [H3 | [H5 | [H7 | [H11 | [H13 | []]]]]]]; subst x.
        -- (* 2 *) split; [|lia]. unfold is_prime. split; [lia|]. intros d Hmin Hmax. lia.
        -- (* 3 *) split; [|lia]. unfold is_prime. split; [lia|]. intros d Hmin Hmax. assert (d=2) by lia. subst. simpl. discriminate.
        -- (* 5 *) split; [|lia]. unfold is_prime. split; [lia|]. intros d Hmin Hmax. assert (d=2\/d=3\/d=4) by lia. destruct H as [?|[?|?]]; subst; simpl; discriminate.
        -- (* 7 *) split; [|lia]. unfold is_prime. split; [lia|]. intros d Hmin Hmax. assert (d=2\/d=3\/d=4\/d=5\/d=6) by lia. destruct H as [?|[?|[?|[?|?]]]]; subst; simpl; discriminate.
        -- (* 11 *) split; [|lia]. unfold is_prime. split; [lia|]. intros d Hmin Hmax. assert (d=2\/d=3\/d=4\/d=5\/d=6\/d=7\/d=8\/d=9\/d=10) by lia. destruct H as [?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]; subst; simpl; discriminate.
        -- (* 13 *) split; [|lia]. unfold is_prime. split; [lia|]. intros d Hmin Hmax. assert (d=2\/d=3\/d=4\/d=5\/d=6\/d=7\/d=8\/d=9\/d=10\/d=11\/d=12) by lia. destruct H as [?|[?|[?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]]]; subst; simpl; discriminate.
      * (* Backward: prime /\ range -> In list *)
        intros [H_prime H_range].
        unfold is_prime in H_prime. destruct H_prime as [H_ge2 H_forall].
        assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11 \/ x = 12 \/ x = 13 \/ x = 14 \/ x = 15 \/ x = 16) as H_cases by lia.
        destruct H_cases as [?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]]]]]]]; subst x; simpl; try tauto.
        all: exfalso.
        1: apply (H_forall 2); [lia|lia|reflexivity]. (* 4 *)
        1: apply (H_forall 2); [lia|lia|reflexivity]. (* 6 *)
        1: apply (H_forall 2); [lia|lia|reflexivity]. (* 8 *)
        1: apply (H_forall 3); [lia|lia|reflexivity]. (* 9 *)
        1: apply (H_forall 2); [lia|lia|reflexivity]. (* 10 *)
        1: apply (H_forall 2); [lia|lia|reflexivity]. (* 12 *)
        1: apply (H_forall 2); [lia|lia|reflexivity]. (* 14 *)
        1: apply (H_forall 3); [lia|lia|reflexivity]. (* 15 *)
        1: apply (H_forall 2); [lia|lia|reflexivity]. (* 16 *)
    + (* Sorted property *)
      intros i j H_lt H_bound.
      simpl in H_bound.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) as Hi by lia.
      destruct Hi as [?|[?|[?|[?|[?|?]]]]]; subst i.
      all: assert (j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) as Hj by lia; destruct Hj as [?|[?|[?|[?|[?|?]]]]]; subst j; try lia; simpl; lia.
Qed.