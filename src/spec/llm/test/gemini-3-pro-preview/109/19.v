Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_cyclic_shift (l1 l2 : list Z) : Prop :=
  exists part1 part2, l1 = part1 ++ part2 /\ l2 = part2 ++ part1.

Definition move_one_ball_spec (arr : list Z) (result : bool) : Prop :=
  result = true <-> (exists l', is_cyclic_shift arr l' /\ Sorted Z.le l').

Example test_move_one_ball : move_one_ball_spec [9%Z; 2%Z; 1%Z] false.
Proof.
  unfold move_one_ball_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [l' [Hshift Hsorted]].
    unfold is_cyclic_shift in Hshift.
    destruct Hshift as [part1 [part2 [Heq1 Heq2]]].
    destruct part1 as [|x1 part1].
    + simpl in Heq1. subst part2.
      simpl in Heq2. subst l'.
      inversion Hsorted as [|? ? Hsort1 Hrel1]; subst.
      inversion Hrel1; subst. lia.
    + simpl in Heq1. injection Heq1 as Hx1 Heq1. subst x1.
      destruct part1 as [|x2 part1].
      * simpl in Heq1. subst part2.
        simpl in Heq2. subst l'.
        inversion Hsorted as [|? ? Hsort1 Hrel1]; subst.
        inversion Hrel1; subst. lia.
      * simpl in Heq1. injection Heq1 as Hx2 Heq1. subst x2.
        destruct part1 as [|x3 part1].
        -- simpl in Heq1. subst part2.
           simpl in Heq2. subst l'.
           inversion Hsorted as [|? ? Hsort1 Hrel1]; subst.
           inversion Hrel1; subst.
           inversion Hsort1 as [|? ? Hsort2 Hrel2]; subst.
           inversion Hrel2; subst. lia.
        -- simpl in Heq1. injection Heq1 as Hx3 Heq1. subst x3.
           destruct part1 as [|x4 part1].
           ++ simpl in Heq1. subst part2.
              simpl in Heq2. subst l'.
              inversion Hsorted as [|? ? Hsort1 Hrel1]; subst.
              inversion Hrel1; subst. lia.
           ++ simpl in Heq1. discriminate.
Qed.