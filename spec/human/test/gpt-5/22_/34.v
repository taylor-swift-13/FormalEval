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

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_22_pre (input : list py_value) : Prop := True.

Definition problem_22_spec (input : list py_value) (output : list py_value) : Prop :=
  is_subsequence output input /\
  (forall v, In v output <-> (In v input /\ is_int v)).

Example problem_22_test :
  problem_22_spec
    [PyInt 8%Z; PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z; PyInt 5%Z; PyInt 1%Z]
    [PyInt 8%Z; PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z; PyInt 5%Z; PyInt 1%Z].
Proof.
  split.
  - repeat constructor.
  - intros v; split.
    + intros Hin. split.
      * exact Hin.
      * destruct Hin as [Heq | Hin1].
        { subst. simpl. exact I. }
        destruct Hin1 as [Heq | Hin2].
        { subst. simpl. exact I. }
        destruct Hin2 as [Heq | Hin3].
        { subst. simpl. exact I. }
        destruct Hin3 as [Heq | Hin4].
        { subst. simpl. exact I. }
        destruct Hin4 as [Heq | Hin5].
        { subst. simpl. exact I. }
        destruct Hin5 as [Heq | Hin6].
        { subst. simpl. exact I. }
        destruct Hin6 as [Heq | Hin7].
        { subst. simpl. exact I. }
        destruct Hin7 as [Heq | Hin8].
        { subst. simpl. exact I. }
        simpl in Hin8. contradiction.
    + intros [Hin Hinter].
      exact Hin.
Qed.