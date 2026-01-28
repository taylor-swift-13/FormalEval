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

Example test_next_smallest_2 :
  problem_90_spec [-10%Z; -20%Z; -51%Z; -30%Z; -40%Z; -50%Z; -60%Z; -70%Z; -79%Z; -90%Z; -100%Z; -110%Z; -10%Z; -70%Z; -60%Z] (Some (-100%Z)).
Proof.
  unfold problem_90_spec.
  exists (-110%Z).
  split.
  - simpl. right. right. right. right. right. right. right. right. right. right. right. left. reflexivity.
  - split.
    + intros x Hx.
      simpl in Hx.
      destruct Hx as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]]]]].
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * subst. lia.
      * contradiction.
    + split.
      * simpl. right. right. right. right. right. right. right. right. right. right. left. reflexivity.
      * split.
        -- lia.
        -- intros y Hy Hlt.
           simpl in Hy.
           destruct Hy as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]]]]].
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ subst. lia.
           ++ contradiction.
Qed.