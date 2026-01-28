Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Import ListNotations.

Definition bool_le (b1 b2 : bool) : Prop :=
  match b1, b2 with
  | false, _ => True
  | _, true => True
  | true, false => False
  end.

Definition problem_34_pre (input : list bool) : Prop := True.

Definition problem_34_spec (input : list bool) (output : list bool) : Prop :=
  Sorted bool_le output /\
  NoDup output /\
  (forall z, In z input <-> In z output).

Example test_problem_34 :
  problem_34_spec [false; false; false; true; true] [false; true].
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
    - simpl. intuition. discriminate.
    - apply NoDup_nil.
  }
  {
    intro z.
    split; intro H.
    - simpl in H.
      repeat destruct H as [H|H]; subst; simpl; auto.
    - simpl in H.
      repeat destruct H as [H|H]; subst; simpl; auto.
  }
Qed.