Require Import Coq.Lists.List.
Require Import Sorting.Sorted.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop := implb b1 b2 = true.

Definition problem_58_pre (l1 l2 : list bool) : Prop := True.

Definition problem_58_spec (l1 l2 l_out: list bool) : Prop :=
  (forall x: bool, In x l_out <-> (In x l1 /\ In x l2)) /\
  Sorted bool_le l_out /\
  NoDup l_out.

Example test_problem_58:
  problem_58_spec
    [true; false; false; false; true; false; false; true; false; false; false; false]
    [true; false; false; false; true; false; false; true; false; false; false; false]
    [false; true].
Proof.
  unfold problem_58_spec.
  split.
  - intro x; destruct x.
    + split; intro H.
      * split; simpl; auto 20.
      * simpl; auto.
    + split; intro H.
      * split; simpl; auto 20.
      * simpl; auto.
  - split.
    + unfold bool_le. repeat constructor.
    + repeat constructor; simpl; intuition discriminate.
Qed.