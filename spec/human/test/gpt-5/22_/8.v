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
    [PyInt 1000000%Z; PyInt (-1000000)%Z; PyFloat; PyString "-1"; PyString "-2"; PyList]
    [PyInt 1000000%Z; PyInt (-1000000)%Z].
Proof.
  split.
  - apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - intros v; split.
    + intros H. simpl in H. destruct H as [H | [H | H]]; [subst v | subst v | contradiction].
      * split. simpl. left. reflexivity. simpl. constructor.
      * split. simpl. right. left. reflexivity. simpl. constructor.
    + intros [Hin Hinter]. simpl in Hin. destruct Hin as [H | [H | [H | [H | [H | [H | Hnil]]]]]].
      * subst v. simpl. left. reflexivity.
      * subst v. simpl. right. left. reflexivity.
      * subst v. simpl in Hinter. contradiction.
      * subst v. simpl in Hinter. contradiction.
      * subst v. simpl in Hinter. contradiction.
      * subst v. simpl in Hinter. contradiction.
      * contradiction.
Qed.