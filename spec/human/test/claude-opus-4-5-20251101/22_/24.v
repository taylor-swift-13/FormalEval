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
  | PyList
  | PyBool (b : bool)
  | PyNone.

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

Definition test_input : list py_value :=
  [PyBool true; PyBool false; PyNone; PyInt 0; PyInt (-10); PyString "test"; PyList; PyDict; PyFloat].

Definition test_output : list py_value :=
  [PyInt 0; PyInt (-10)].

Lemma is_int_PyInt : forall n, is_int (PyInt n).
Proof.
  intro n. simpl. exact I.
Qed.

Lemma not_is_int_PyBool : forall b, ~is_int (PyBool b).
Proof.
  intro b. simpl. auto.
Qed.

Lemma not_is_int_PyNone : ~is_int PyNone.
Proof.
  simpl. auto.
Qed.

Lemma not_is_int_PyString : forall s, ~is_int (PyString s).
Proof.
  intro s. simpl. auto.
Qed.

Lemma not_is_int_PyList : ~is_int PyList.
Proof.
  simpl. auto.
Qed.

Lemma not_is_int_PyDict : ~is_int PyDict.
Proof.
  simpl. auto.
Qed.

Lemma not_is_int_PyFloat : ~is_int PyFloat.
Proof.
  simpl. auto.
Qed.

Example test_filter_integers_2 :
  problem_22_spec test_input test_output.
Proof.
  unfold problem_22_spec, test_input, test_output.
  split.
  - apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_nil.
  - intro v.
    split.
    + intro H.
      simpl in H.
      destruct H as [H | [H | H]].
      * subst v.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- apply is_int_PyInt.
      * subst v.
        split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- apply is_int_PyInt.
      * contradiction.
    + intro H.
      destruct H as [H1 H2].
      simpl in H1.
      destruct H1 as [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | [H1 | H1]]]]]]]]].
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl. left. reflexivity.
      * subst v. simpl. right. left. reflexivity.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * subst v. simpl in H2. contradiction.
      * contradiction.
Qed.