Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Definition problem_58_pre (l1 l2 : list Z) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list Z) : Prop :=
  (forall x: Z, In x l_out <-> (In x l1 /\ In x l2)) /\
  Sorted Z.le l_out /\
  NoDup l_out.

Example test_common_2 :
  problem_58_spec [4%Z; 3%Z; 2%Z; 8%Z] 
                  [3%Z; 2%Z; 4%Z] 
                  [2%Z; 3%Z; 4%Z].
Proof.
  unfold problem_58_spec.
  split; [| split].
  - intro x.
    split.
    + intro H.
      simpl in H.
      destruct H as [H | [H | [H | H]]].
      * subst x. split; simpl; auto.
      * subst x. split; simpl; auto.
      * subst x. split; simpl; auto.
      * contradiction.
    + intros [H1 H2].
      simpl in H1, H2.
      simpl.
      destruct H1 as [H1 | [H1 | [H1 | [H1 | H1]]]];
      destruct H2 as [H2 | [H2 | [H2 | H2]]];
      try subst x; try (left; reflexivity); try (right; left; reflexivity); 
      try (right; right; left; reflexivity); try contradiction; try lia.
  - repeat constructor; lia.
  - constructor.
    + simpl. intros [H | [H | H]]; lia.
    + constructor.
      * simpl. intros [H | H]; lia.
      * constructor.
        -- simpl. intros H. contradiction.
        -- constructor.
Qed.