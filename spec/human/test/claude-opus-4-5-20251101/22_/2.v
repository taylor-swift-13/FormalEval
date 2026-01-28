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
  problem_22_spec [PyInt 4; PyDict; PyList; PyFloat; PyInt 9; PyString "adasd"%string] [PyInt 4; PyInt 9].
Proof.
  unfold problem_22_spec.
  split.
  - apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_nil.
  - intro v.
    split.
    + intro H.
      simpl in H.
      destruct H as [H | [H | H]].
      * subst v.
        split.
        -- simpl. left. reflexivity.
        -- simpl. exact I.
      * subst v.
        split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- simpl. exact I.
      * contradiction.
    + intro H.
      destruct H as [H1 H2].
      simpl in H1.
      destruct H1 as [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]].
      * subst v. simpl. left. reflexivity.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl. right. left. reflexivity.
      * subst v. simpl in H2. contradiction.
      * contradiction.
Qed.