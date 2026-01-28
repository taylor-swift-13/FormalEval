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

Example test_filter_integers_all_ints :
  problem_22_spec [PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z] 
                  [PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z].
Proof.
  unfold problem_22_spec.
  split.
  - simpl.
    left. split. reflexivity.
    left. split. reflexivity.
    left. split. reflexivity.
    left. split. reflexivity.
    left. split. reflexivity.
    trivial.
  - intro v.
    split.
    + intro H.
      split.
      * exact H.
      * simpl in H.
        destruct H as [H|[H|[H|[H|[H|H]]]]];
        rewrite <- H; simpl; trivial.
    + intros [H1 H2].
      simpl in H1.
      destruct H1 as [H1|[H1|[H1|[H1|[H1|H1]]]]].
      * left. exact H1.
      * right. left. exact H1.
      * right. right. left. exact H1.
      * right. right. right. left. exact H1.
      * right. right. right. right. left. exact H1.
      * contradiction.
Qed.