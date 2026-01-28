Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  match b1 with
  | false => True
  | true => b2 = true
  end.

Definition problem_58_pre (l1 l2 : list bool) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list bool) : Prop :=
  (forall x: bool, In x l_out <-> (In x l1 /\ In x l2)) /\
  Sorted bool_le l_out /\
  NoDup l_out.

Example test_problem_58:
  problem_58_spec
    [false; true]
    [false; true]
    [false; true].
Proof.
  unfold problem_58_spec.
  split.
  - intro x; split.
    + intro H.
      simpl in H.
      repeat destruct H as [H|H]; subst; simpl; split; auto.
    + intros [H1 H2].
      simpl in H1.
      repeat destruct H1 as [H1|H1]; subst; simpl; auto; try contradiction.
  - split.
    + repeat constructor.
    + repeat constructor; simpl; intuition discriminate.
Qed.