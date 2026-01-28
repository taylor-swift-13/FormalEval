Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition is_cyclic_shift (l1 l2 : list Z) : Prop :=
  exists part1 part2, l1 = part1 ++ part2 /\ l2 = part2 ++ part1.

Definition move_one_ball_spec (arr : list Z) (result : bool) : Prop :=
  result = true <-> (exists l', is_cyclic_shift arr l' /\ Sorted Z.le l').

Example test_move_one_ball : move_one_ball_spec [7%Z; 8%Z; 6%Z; 4%Z; 5%Z; 3%Z; 1%Z; 2%Z] false.
Proof.
  unfold move_one_ball_spec.
  split.
  - intro H. discriminate.
  - intros [l' [Hshift Hsorted]].
    unfold is_cyclic_shift in Hshift.
    destruct Hshift as [p1 [p2 [Heq1 Heq2]]].
    repeat match goal with
    | [ H : ?L = p1 ++ p2 |- _ ] =>
      destruct p1 as [|? p1]; simpl in H;
      [ subst;
        repeat match goal with
        | [ H : Sorted _ _ |- _ ] => inversion H; subst; clear H
        | [ H : HdRel _ _ _ |- _ ] => inversion H; subst; clear H
        end; try lia
      | inversion H; subst; clear H ]
    end.
Qed.