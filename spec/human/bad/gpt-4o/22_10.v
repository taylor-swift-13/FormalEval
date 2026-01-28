Require Import Coq.Lists.List.
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

Example test_case_1 : problem_22_spec 
  [PyInt 1%Z; PyInt (-1)%Z; PyInt 0%Z; PyInt 999%Z]
  [PyInt 1%Z; PyInt (-1)%Z; PyInt 0%Z; PyInt 999%Z].
Proof.
  unfold problem_22_spec.
  split.
  - simpl. repeat split; try apply is_subsequence; simpl; auto.
  - intros v. split.
    + intros H. repeat (destruct H as [H | H]; subst; auto).
    + intros [H_in H_int]. repeat (destruct H_in as [H | H]; subst; auto).
Qed.