Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_90_pre (l : list Z) : Prop := True.

Definition problem_90_spec (l : list Z) (res : option Z) : Prop :=
  match res with
  | Some z =>
    exists s1,
      In s1 l /\
      (forall x, In x l -> s1 <= x) /\
      In z l /\
      s1 < z /\
      (forall y, In y l -> s1 < y -> z <= y)
  | None =>
    ~ (exists x y, In x l /\ In y l /\ x <> y)
  end.

Example test_next_smallest_1 :
  problem_90_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z] (Some 2%Z).
Proof.
  unfold problem_90_spec.
  exists 1%Z.
  split.
  - (* In 1 [1; 2; 3; 4; 5] *)
    simpl. left. reflexivity.
  - split.
    + (* forall x, In x [1; 2; 3; 4; 5] -> 1 <= x *)
      intros x Hx.
      simpl in Hx.
      destruct Hx as [H | [H | [H | [H | [H | H]]]]].
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * contradiction.
    + split.
      * (* In 2 [1; 2; 3; 4; 5] *)
        simpl. right. left. reflexivity.
      * split.
        -- (* 1 < 2 *)
           lia.
        -- (* forall y, In y [1; 2; 3; 4; 5] -> 1 < y -> 2 <= y *)
           intros y Hy Hlt.
           simpl in Hy.
           destruct Hy as [H | [H | [H | [H | [H | H]]]]].
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ contradiction.
Qed.