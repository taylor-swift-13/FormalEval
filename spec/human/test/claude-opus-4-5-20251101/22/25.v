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
  | PyList
  | PyBool (b : bool)
  | PyNone.

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

Example test_filter_integers_complex :
  problem_22_spec [PyDict; PyBool true; PyBool false; PyNone; PyInt 0; PyInt (-10); PyString "test"; PyList; PyDict; PyFloat] [PyInt 0; PyInt (-10)].
Proof.
  unfold problem_22_spec.
  split.
  - simpl.
    right. right. right. right.
    left. split. reflexivity.
    left. split. reflexivity.
    trivial.
  - intro v.
    split.
    + intro H.
      simpl in H.
      destruct H as [H | [H | H]].
      * subst v. split.
        simpl. right. right. right. right. left. reflexivity.
        simpl. trivial.
      * subst v. split.
        simpl. right. right. right. right. right. left. reflexivity.
        simpl. trivial.
      * contradiction.
    + intros [H1 H2].
      simpl in H1.
      destruct H1 as [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]]]]].
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl. left. reflexivity.
      * subst v. simpl. right. left. reflexivity.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * contradiction.
Qed.