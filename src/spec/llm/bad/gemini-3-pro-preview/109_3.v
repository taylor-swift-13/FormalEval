Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_cyclic_shift (l1 l2 : list Z) : Prop :=
  exists part1 part2, l1 = part1 ++ part2 /\ l2 = part2 ++ part1.

Definition move_one_ball_spec (arr : list Z) (result : bool) : Prop :=
  result = true <-> (exists l', is_cyclic_shift arr l' /\ Sorted Z.le l').

Example test_move_one_ball : move_one_ball_spec [4%Z; 3%Z; 1%Z; 2%Z] false.
Proof.
  unfold move_one_ball_spec.
  split.
  - intros H. discriminate.
  - intros [l' [Hshift Hsorted]].
    unfold is_cyclic_shift in Hshift.
    destruct Hshift as [part1 [part2 [H1 H2]]].
    destruct part1 as [|p1 [|p2 [|p3 [|p4 [|p5 part1]]]]].
    + simpl in H1. subst part2. simpl in H2. subst l'.
      repeat match goal with
      | H : Sorted _ _ |- _ => inversion H; subst; clear H
      | H : HdRel _ _ _ _ |- _ => inversion H; subst; clear H
      end; try lia.
    + simpl in H1. inversion H1; subst. simpl in H2. subst l'.
      repeat match goal with
      | H : Sorted _ _ |- _ => inversion H; subst; clear H
      | H : HdRel _ _ _ _ |- _ => inversion H; subst; clear H
      end; try lia.
    + simpl in H1. inversion H1; subst. simpl in H2. subst l'.
      repeat match goal with
      | H : Sorted _ _ |- _ => inversion H; subst; clear H
      | H : HdRel _ _ _ _ |- _ => inversion H; subst; clear H
      end; try lia.
    + simpl in H1. inversion H1; subst. simpl in H2. subst l'.
      repeat match goal with
      | H : Sorted _ _ |- _ => inversion H; subst; clear H
      | H : HdRel _ _ _ _ |- _ => inversion H; subst; clear H
      end; try lia.
    + simpl in H1. inversion H1; subst. destruct part2; [|discriminate].
      simpl in H2. subst l'.
      repeat match goal with
      | H : Sorted _ _ |- _ => inversion H; subst; clear H
      | H : HdRel _ _ _ _ |- _ => inversion H; subst; clear H
      end; try lia.
    + simpl in H1. discriminate.
Qed.