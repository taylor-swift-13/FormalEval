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
    [PyString "apple"; PyFloat; PyDict; PyList; PyString "watermelon"; PyInt 42%Z; PyFloat]
    [PyInt 42%Z].
Proof.
  split.
  - apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    constructor.
  - intros v; split.
    + intros H. simpl in H. destruct H as [Heq | Hnil].
      * subst v. split.
        -- simpl. right. right. right. right. right. left. reflexivity.
        -- simpl. exact I.
      * contradiction.
    + intros [Hin Hinter].
      destruct v; simpl in Hinter; try contradiction.
      simpl in Hin.
      destruct Hin as [H0 | [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]]].
      * inversion H0.
      * inversion H1.
      * inversion H2.
      * inversion H3.
      * inversion H4.
      * inversion H5; subst.
        simpl. left. reflexivity.
      * inversion H6.
      * contradiction.
Qed.