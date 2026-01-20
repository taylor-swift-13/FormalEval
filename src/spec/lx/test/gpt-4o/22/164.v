Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Inductive py_value : Type :=
  | PyInt (n : Z)
  | PyString (s : string)
  | PyFloat
  | PyDict
  | PyList (l : list py_value).

Definition is_int (v : py_value) : Prop :=
  match v with
  | PyInt _ => True
  | _       => False
  end.

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : is_subsequence [] []
  | sub_cons_hd : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_tl : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition Spec (input : list py_value) (output : list py_value) : Prop :=
  is_subsequence output input /\
  (forall v, In v output <-> (In v input /\ is_int v)).

Example filter_integers_test_nested :
  Spec [PyList [PyInt 4; PyInt 5]; PyInt 8] [PyInt 8].
Proof.
  unfold Spec.
  split.
  - apply sub_cons_tl. apply sub_cons_hd. apply sub_nil.
  - intros v. split.
    + intros H. destruct H as [H | H].
      * subst. split.
        -- right. left. reflexivity.
        -- simpl. reflexivity.
      * inversion H.
    + intros [H1 H2]. destruct H1 as [H1 | H1].
      * inversion H1. subst. inversion H2.
      * destruct H1 as [H1 | H1].
        -- subst. left. reflexivity.
        -- inversion H1.
Qed.