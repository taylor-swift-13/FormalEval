Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  match b1, b2 with
  | true, false => False
  | _, _ => True
  end.

Definition problem_34_pre (input : list bool) : Prop := True.

Definition problem_34_spec (input : list bool) (output : list bool) : Prop :=
  Sorted bool_le output /\
  NoDup output /\
  (forall b, In b input <-> In b output).

Example test_problem_34 :
  problem_34_spec [false; true; false; false; true; false] [false; true].
Proof.
  unfold problem_34_spec.
  split.
  {
    repeat apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
    - apply HdRel_cons. simpl. exact I.
  }
  split.
  {
    repeat apply NoDup_cons.
    - simpl. intuition discriminate.
    - simpl. intuition.
    - apply NoDup_nil.
  }
  {
    intro b.
    split; intro H; simpl in *; intuition; destruct b; intuition.
  }
Qed.