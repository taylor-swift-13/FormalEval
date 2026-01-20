Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition generate_integers_spec (a b : Z) (l : list Z) : Prop :=
  let lower := Z.min a b in
  let upper := Z.max a b in
  Sorted Z.lt l /\
  (forall x : Z, In x l <-> lower <= x <= upper /\ x < 10 /\ Z.even x = true).

Example test_generate_integers : generate_integers_spec 2 10 [2; 4; 6; 8].
Proof.
  unfold generate_integers_spec.
  simpl.
  split.
  - (* Prove Sorted Z.lt [2; 4; 6; 8] *)
    repeat constructor; lia.
  - (* Prove the membership equivalence *)
    intro x.
    split.
    + (* In x [2; 4; 6; 8] -> conditions *)
      intro H.
      simpl in H.
      destruct H as [H | [H | [H | [H | H]]]].
      * subst x. repeat split; try reflexivity; lia.
      * subst x. repeat split; try reflexivity; lia.
      * subst x. repeat split; try reflexivity; lia.
      * subst x. repeat split; try reflexivity; lia.
      * contradiction.
    + (* conditions -> In x [2; 4; 6; 8] *)
      intro H.
      destruct H as [[Hlower Hupper] [Hlt10 Heven]].
      simpl.
      (* x is even, >= 2, <= 10, and < 10, so x in {2, 4, 6, 8} *)
      assert (x = 2 \/ x = 4 \/ x = 6 \/ x = 8).
      {
        destruct (Z.even x) eqn:Heq; try discriminate.
        (* x is even and 2 <= x < 10 *)
        assert (x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8 \/ x = 9) by lia.
        destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; simpl in Heq; try discriminate; auto.
      }
      destruct H as [H|[H|[H|H]]]; subst; auto.
Qed.