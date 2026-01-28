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

Example test_count_up_to_5: count_up_to_spec 5 [2; 3].
Proof.
  unfold count_up_to_spec.
  split.
  - (* n >= 0 *)
    lia.
  - split.
    + (* Membership property: forall x, In x result <-> is_prime x /\ 2 <= x < n *)
      intros x.
      split.
      * (* Forward: In x [2; 3] -> is_prime x /\ 2 <= x < 5 *)
        intros H_in.
        simpl in H_in.
        destruct H_in as [H_eq2 | [H_eq3 | H_false]].
        -- (* x = 2 *)
           subst x.
           split.
           ++ unfold is_prime. split. lia.
              intros d H_min H_max. lia.
           ++ lia.
        -- (* x = 3 *)
           subst x.
           split.
           ++ unfold is_prime. split. lia.
              intros d H_min H_max.
              assert (d = 2) by lia. subst d.
              intro H_div. compute in H_div. discriminate.
           ++ lia.
        -- (* False case from end of list *)
           contradiction.
      * (* Backward: is_prime x /\ 2 <= x < 5 -> In x [2; 3] *)
        intros [H_prime H_range].
        unfold is_prime in H_prime.
        destruct H_prime as [H_ge2 H_forall].
        (* Possible values for x in [2, 5) are 2, 3, 4 *)
        assert (x = 2 \/ x = 3 \/ x = 4) as H_cases by lia.
        destruct H_cases as [H2 | [H3 | H4]].
        -- subst x. simpl. left. reflexivity.
        -- subst x. simpl. right. left. reflexivity.
        -- subst x.
           exfalso.
           (* 4 is not prime because it is divisible by 2 *)
           apply (H_forall 2).
           ++ lia.
           ++ lia.
           ++ reflexivity.
    + (* Sorted property: indices i < j imply nth i < nth j *)
      intros i j H_lt H_bound.
      simpl in H_bound.
      (* length [2; 3] is 2, so j < 2. Since 0 <= i < j, we must have i=0 and j=1 *)
      assert (i = 0 /\ j = 1) as H_indices by lia.
      destruct H_indices; subst.
      simpl.
      lia.
Qed.