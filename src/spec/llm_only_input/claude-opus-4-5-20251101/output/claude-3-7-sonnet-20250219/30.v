Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [-1%Z; -2%Z; 4%Z; 5%Z; 6%Z] [4%Z; 5%Z; 6%Z].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | H]]].
    + subst x. split; [simpl; right; right; left; reflexivity | lia].
    + subst x. split; [simpl; right; right; right; left; reflexivity | lia].
    + subst x. split; [simpl; right; right; right; right; left; reflexivity | lia].
    + contradiction.
  - intros x H Hpos.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + subst x. lia.
    + subst x. lia.
    + subst x. simpl. left. reflexivity.
    + subst x. simpl. right. left. reflexivity.
    + subst x. simpl. right. right. left. reflexivity.
    + contradiction.
Qed.