Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive py_value : Type :=
  | PyInt (n : nat)
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
  | sub_nil : is_subsequence [] []
  | sub_cons_hd : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_tl : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition Spec (input : list py_value) (output : list py_value) : Prop :=
  is_subsequence output input /\
  (forall v, In v output <-> (In v input /\ is_int v)).

Example filter_integers_test_empty_dicts :
  Spec [] [].
Proof.
  unfold Spec.
  split.
  - apply sub_nil.
  - intros v. split.
    + intros H. inversion H.
    + intros [H _]. inversion H.
Qed.