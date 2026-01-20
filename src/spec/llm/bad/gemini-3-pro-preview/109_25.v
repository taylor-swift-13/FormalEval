Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_cyclic_shift (l1 l2 : list Z) : Prop :=
  exists part1 part2, l1 = part1 ++ part2 /\ l2 = part2 ++ part1.

Definition move_one_ball_spec (arr : list Z) (result : bool) : Prop :=
  result = true <-> (exists l', is_cyclic_shift arr l' /\ Sorted Z.le l').

Example test_move_one_ball : move_one_ball_spec [4%Z; 3%Z; 2%Z] false.
Proof.
  unfold move_one_ball_spec.
  split.
  - intros H. discriminate H.
  - intros [l' [Hshift Hsorted]].
    unfold is_cyclic_shift in Hshift.
    destruct Hshift as [p1 [p2 [Heq Hl']]].
    subst l'.
    destruct p1; simpl in Heq.
    + injection Heq as Heq. subst p2.
      repeat (match goal with | H: Sorted _ _ |- _ => inversion H; subst; clear H | H: HdRel _ _ _ |- _ => inversion H; subst; clear H end); try lia.
    + destruct p1; simpl in Heq.
      * injection Heq as Hz Heq. subst.
        repeat (match goal with | H: Sorted _ _ |- _ => inversion H; subst; clear H | H: HdRel _ _ _ |- _ => inversion H; subst; clear H end); try lia.
      * destruct p1; simpl in Heq.
        -- injection Heq as Hz Hz0 Heq. subst.
           repeat (match goal with | H: Sorted _ _ |- _ => inversion H; subst; clear H | H: HdRel _ _ _ |- _ => inversion H; subst; clear H end); try lia.
        -- destruct p1; simpl in Heq.
           ++ injection Heq as Hz Hz0 Hz1 Heq. subst.
              repeat (match goal with | H: Sorted _ _ |- _ => inversion H; subst; clear H | H: HdRel _ _ _ |- _ => inversion H; subst; clear H end); try lia.
           ++ discriminate.
Qed.