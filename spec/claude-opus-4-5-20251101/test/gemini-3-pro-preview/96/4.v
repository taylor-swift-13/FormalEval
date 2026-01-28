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

Example test_count_up_to_10: count_up_to_spec 10 [2; 3; 5; 7].
Proof.
  unfold count_up_to_spec.
  split.
  - (* n >= 0 *)
    lia.
  - split.
    + (* Membership property *)
      intros x.
      split.
      * (* Forward: In x [2; 3; 5; 7] -> is_prime x /\ 2 <= x < 10 *)
        intros H_in.
        simpl in H_in.
        destruct H_in as [H2 | [H3 | [H5 | [H7 | []]]]]; subst x.
        -- (* x = 2 *)
           split.
           ++ unfold is_prime. split. lia.
              intros d H_min H_max. lia.
           ++ lia.
        -- (* x = 3 *)
           split.
           ++ unfold is_prime. split. lia.
              intros d H_min H_max.
              assert (d = 2) by lia. subst d.
              intro H_div. compute in H_div. discriminate.
           ++ lia.
        -- (* x = 5 *)
           split.
           ++ unfold is_prime. split. lia.
              intros d H_min H_max.
              assert (d = 2 \/ d = 3 \/ d = 4) by lia.
              destruct H as [? | [? | ?]]; subst d;
              intro H_div; compute in H_div; discriminate.
           ++ lia.
        -- (* x = 7 *)
           split.
           ++ unfold is_prime. split. lia.
              intros d H_min H_max.
              assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6) by lia.
              destruct H as [? | [? | [? | [? | ?]]]]; subst d;
              intro H_div; compute in H_div; discriminate.
           ++ lia.
      * (* Backward: is_prime x /\ 2 <= x < 10 -> In x [2; 3; 5; 7] *)
        intros [H_prime H_range].
        unfold is_prime in H_prime.
        destruct H_prime as [H_ge2 H_forall].
        assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9) as H_cases by lia.
        repeat destruct H_cases as [H_eq | H_cases]; subst x; simpl.
        -- left. reflexivity.
        -- right. left. reflexivity.
        -- exfalso. apply (H_forall 2). lia. lia. reflexivity.
        -- right. right. left. reflexivity.
        -- exfalso. apply (H_forall 2). lia. lia. reflexivity.
        -- right. right. right. left. reflexivity.
        -- exfalso. apply (H_forall 2). lia. lia. reflexivity.
        -- exfalso. apply (H_forall 3). lia. lia. reflexivity.
    + (* Sorted property *)
      intros i j H_lt H_bound.
      simpl in H_bound.
      assert (j = 1 \/ j = 2 \/ j = 3) as Hj by lia.
      destruct Hj as [Hj1 | [Hj2 | Hj3]]; subst j.
      * (* j = 1 *)
        assert (i = 0) by lia. subst i.
        simpl. lia.
      * (* j = 2 *)
        assert (i = 0 \/ i = 1) as Hi by lia.
        destruct Hi; subst i; simpl; lia.
      * (* j = 3 *)
        assert (i = 0 \/ i = 1 \/ i = 2) as Hi by lia.
        destruct Hi as [| [|]]; subst i; simpl; lia.
Qed.