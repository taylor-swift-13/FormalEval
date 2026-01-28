Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition bool_le (x y : bool) : Prop :=
  match x, y with
  | true, false => False
  | _, _ => True
  end.

Definition problem_34_pre (input : list bool) : Prop := True.

Definition problem_34_spec (input : list bool) (output : list bool) : Prop :=
  Sorted bool_le output /\
  NoDup output /\
  (forall x, In x input <-> In x output).

Example test_problem_34 :
  problem_34_spec [true] [true].
Proof.
  unfold problem_34_spec.
  split.
  {
    apply Sorted_cons.
    - apply Sorted_nil.
    - apply HdRel_nil.
  }
  split.
  {
    apply NoDup_cons.
    - simpl. intuition.
    - apply NoDup_nil.
  }
  {
    intro x.
    split; intro H; assumption.
  }
Qed.