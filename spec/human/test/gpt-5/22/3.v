Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Import ListNotations.

Inductive py_value : Type :=
  | PyInt (n : Z)
  | PyString (s : string)
  | PyFloat
  | PyDict
  | PyList.

Definition is_int (v : py_value) : Prop :=
  match v with
  | PyInt _ => True
  | _       => False
  end.

Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

Definition problem_22_pre (input : list py_value) : Prop := True.

Definition problem_22_spec (input : list py_value) (output : list py_value) : Prop :=
  is_subsequence output input /\
  (forall v, In v output <-> (In v input /\ is_int v)).

Example problem_22_test_case_mixed_list :
  problem_22_spec
    [PyInt 3%Z; PyString "c"; PyInt 3%Z; PyInt 3%Z; PyString "a"; PyString "b"]
    [PyInt 3%Z; PyInt 3%Z; PyInt 3%Z].
Proof.
  unfold problem_22_spec.
  split.
  - simpl. left. split.
    + reflexivity.
    + simpl. right.
      simpl. left. split.
      * reflexivity.
      * simpl. left. split.
        { reflexivity. }
        { simpl. exact I. }
  - intro v. split.
    + intro H. simpl in H. destruct H as [H | [H | [H | H]]].
      * subst. split.
        { simpl. left. reflexivity. }
        { simpl. exact I. }
      * subst. split.
        { simpl. right. simpl. right. simpl. left. reflexivity. }
        { simpl. exact I. }
      * subst. split.
        { simpl. right. simpl. right. simpl. right. simpl. left. reflexivity. }
        { simpl. exact I. }
      * contradiction.
    + intros [Hin Hint]. simpl in Hin.
      destruct Hin as [H | Hin1].
      * subst. simpl. left. reflexivity.
      * simpl in Hin1.
        destruct Hin1 as [H | Hin2].
        { subst. simpl in Hint. contradiction. }
        { simpl in Hin2.
          destruct Hin2 as [H | Hin3].
          - subst. simpl. left. reflexivity.
          - simpl in Hin3.
            destruct Hin3 as [H | Hin4].
            + subst. simpl. left. reflexivity.
            + simpl in Hin4.
              destruct Hin4 as [H | Hin5].
              { subst. simpl in Hint. contradiction. }
              { simpl in Hin5.
                destruct Hin5 as [H | Hin6].
                - subst. simpl in Hint. contradiction.
                - contradiction. } }
Qed.