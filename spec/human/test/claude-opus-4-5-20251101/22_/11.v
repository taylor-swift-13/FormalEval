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

Example test_filter_integers_2 :
  problem_22_spec [PyInt 0%Z; PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z; PyInt 6%Z; PyInt 7%Z; PyInt 8%Z; PyInt 9%Z] 
                  [PyInt 0%Z; PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z; PyInt 6%Z; PyInt 7%Z; PyInt 8%Z; PyInt 9%Z].
Proof.
  unfold problem_22_spec.
  split.
  - repeat (apply sub_cons_match).
    apply sub_nil.
  - intro v.
    split.
    + intro H.
      split.
      * exact H.
      * simpl in H.
        destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]];
        try (rewrite <- H; simpl; exact I);
        contradiction.
    + intro H.
      destruct H as [H1 H2].
      exact H1.
Qed.