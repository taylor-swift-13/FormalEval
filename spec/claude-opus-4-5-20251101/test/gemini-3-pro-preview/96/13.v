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

Example test_count_up_to_12: count_up_to_spec 12 [2; 3; 5; 7; 11].
Proof.
  unfold count_up_to_spec.
  split.
  - (* n >= 0 *)
    lia.
  - split.
    + (* Membership property *)
      intros x.
      split.
      * (* Forward *)
        intros H_in.
        simpl in H_in.
        destruct H_in as [H2 | [H3 | [H5 | [H7 | [H11 | H_false]]]]].
        -- subst x. split; [|lia].
           unfold is_prime. split; [lia|].
           intros d Hmin Hmax. lia.
        -- subst x. split; [|lia].
           unfold is_prime. split; [lia|].
           intros d Hmin Hmax. assert (d = 2) by lia. subst d.
           intro C. compute in C. discriminate.
        -- subst x. split; [|lia].
           unfold is_prime. split; [lia|].
           intros d Hmin Hmax.
           assert (H: d = 2 \/ d = 3 \/ d = 4) by lia.
           repeat (destruct H as [-> | H]); try subst;
           intro C; compute in C; discriminate.
        -- subst x. split; [|lia].
           unfold is_prime. split; [lia|].
           intros d Hmin Hmax.
           assert (H: d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
           repeat (destruct H as [-> | H]); try subst;
           intro C; compute in C; discriminate.
        -- subst x. split; [|lia].
           unfold is_prime. split; [lia|].
           intros d Hmin Hmax.
           assert (H: d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9 \/ d = 10) by lia.
           repeat (destruct H as [-> | H]); try subst;
           intro C; compute in C; discriminate.
        -- contradiction.
      * (* Backward *)
        intros [H_prime H_range].
        unfold is_prime in H_prime.
        destruct H_prime as [H_ge2 H_forall].
        assert (H_cases: x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9 \/ x = 10 \/ x = 11) by lia.
        destruct H_cases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
        -- simpl. left. reflexivity.
        -- simpl. right. left. reflexivity.
        -- exfalso. apply (H_forall 2); [lia|lia|]. reflexivity.
        -- simpl. right. right. left. reflexivity.
        -- exfalso. apply (H_forall 2); [lia|lia|]. reflexivity.
        -- simpl. right. right. right. left. reflexivity.
        -- exfalso. apply (H_forall 2); [lia|lia|]. reflexivity.
        -- exfalso. apply (H_forall 3); [lia|lia|]. reflexivity.
        -- exfalso. apply (H_forall 2); [lia|lia|]. reflexivity.
        -- simpl. right. right. right. right. left. reflexivity.
    + (* Sorted property *)
      intros i j H_lt H_bound.
      simpl in H_bound.
      assert (Hi: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      assert (Hj: j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4) by lia.
      destruct Hi as [-> | [-> | [-> | [-> | ->]]]];
      destruct Hj as [-> | [-> | [-> | [-> | ->]]]];
      simpl; lia.
Qed.