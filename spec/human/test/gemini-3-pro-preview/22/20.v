Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Import ListNotations.
Open Scope string_scope.

Inductive py_value : Type :=
  | PyInt (n : Z)
  | PyString (s : string)
  | PyFloat
  | PyDict
  | PyList
  | PyNone
  | PyBool (b : bool).

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

Example test_problem_22 : problem_22_spec 
  [PyString "apple"; PyFloat; PyNone; PyBool false; PyString "watermelon"; PyInt 42%Z; PyFloat] 
  [PyInt 42%Z].
Proof.
  unfold problem_22_spec.
  split.
  - simpl. tauto.
  - intros v. split.
    + intros H. simpl in H. destruct H as [H | H]; [| contradiction].
      subst. split.
      * simpl. tauto.
      * simpl. exact I.
    + intros [Hin Hint].
      simpl in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst; simpl in Hint; try contradiction; try (left; reflexivity) | ]).
      contradiction.
Qed.