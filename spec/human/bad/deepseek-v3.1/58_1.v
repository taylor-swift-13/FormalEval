Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Import ListNotations.

Definition problem_58_pre (l1 l2 : list Z) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list Z) : Prop :=
  (forall x: Z, In x l_out <-> (In x l1 /\ In x l2)) /\
  Sorted Z.le l_out /\
  NoDup l_out.

Lemma problem_58_example :
  problem_58_spec [1%Z; 4%Z; 3%Z; 34%Z; 653%Z; 2%Z; 5%Z]
                  [5%Z; 7%Z; 1%Z; 5%Z; 9%Z; 653%Z; 121%Z]
                  [1%Z; 5%Z; 653%Z].
Proof.
  unfold problem_58_spec.
  split. {
    intro x.
    split.
    - intro H.
      simpl in H.
      destruct H as [H|H].
      + subst x. split; simpl; auto.
      + destruct H as [H|H].
        { subst x. split; simpl; auto. }
        destruct H as [H|H].
        { subst x. split; simpl; auto. }
        contradiction.
    - intro H.
      destruct H as [H1 H2].
      simpl in H1, H2.
      destruct H1 as [H1|H1].
      + subst x.
        destruct H2 as [H2|H2].
        { subst x. simpl; auto. }
        destruct H2 as [H2|H2].
        { subst x. simpl; auto. }
        destruct H2 as [H2|H2].
        { subst x. simpl; auto. }
        destruct H2 as [H2|H2].
        { subst x. simpl; auto. }
        destruct H2 as [H2|H2].
        { subst x. simpl; auto. }
        destruct H2 as [H2|H2].
        { subst x. simpl; auto. }
        contradiction.
      + destruct H1 as [H1|H1].
        { subst x.
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          contradiction. }
        destruct H1 as [H1|H1].
        { subst x.
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          contradiction. }
        destruct H1 as [H1|H1].
        { subst x.
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          contradiction. }
        destruct H1 as [H1|H1].
        { subst x.
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          contradiction. }
        destruct H1 as [H1|H1].
        { subst x.
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          contradiction. }
        destruct H1 as [H1|H1].
        { subst x.
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          destruct H2 as [H2|H2].
          { subst x. simpl; auto. }
          contradiction. }
        contradiction.
  }
  split.
  - repeat constructor; apply Z.le_refl.
  - repeat constructor.
Qed.