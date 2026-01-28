Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope.

Inductive py_value : Type :=
  | PyInt (n : Z)
  | PyString (s : string)
  | PyFloat
  | PyDict
  | PyList
  | PyListR (l : list R).

Definition is_int (v : py_value) : Prop :=
  match v with
  | PyInt _ => True
  | _       => False
  end.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_22_pre (input : list py_value) : Prop := True.

Definition problem_22_spec (input : list py_value) (output : list py_value) : Prop :=
  is_subsequence output input /\
  (forall v, In v output <-> (In v input /\ is_int v)).

Example problem_22_test :
  problem_22_spec [PyListR [1.5%R; 2.7%R; 3.0%R; -4.6%R; 1.5%R; 1.5%R]] [].
Proof.
  split.
  - constructor.
  - intros v; split.
    + intros H. simpl in H. contradiction.
    + intros [Hin Hinter]. simpl in Hin. destruct Hin as [Heq | Hin0].
      * subst v. simpl in Hinter. contradiction.
      * contradiction.
Qed.