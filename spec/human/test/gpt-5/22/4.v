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

Example problem_22_test_case_input_list_of_integers :
  problem_22_spec
    [PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z]
    [PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z].
Proof.
  unfold problem_22_spec.
  split.
  - simpl.
    left. split; [reflexivity |].
    simpl.
    left. split; [reflexivity |].
    simpl.
    left. split; [reflexivity |].
    simpl.
    left. split; [reflexivity |].
    simpl.
    left. split; [reflexivity |].
    simpl. exact I.
  - intro v. split.
    + intro H. simpl in H.
      destruct H as [H | [H | [H | [H | [H | Hfalse]]]]].
      * subst v. split.
        -- simpl. left. reflexivity.
        -- simpl. exact I.
      * subst v. split.
        -- simpl. right. left. reflexivity.
        -- simpl. exact I.
      * subst v. split.
        -- simpl. right. right. left. reflexivity.
        -- simpl. exact I.
      * subst v. split.
        -- simpl. right. right. right. left. reflexivity.
        -- simpl. exact I.
      * subst v. split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- simpl. exact I.
      * simpl in Hfalse. contradiction.
    + intros [Hin Hint]. simpl in Hin.
      destruct Hin as [H1 | [H2 | [H3 | [H4 | [H5 | Hfalse]]]]].
      * subst v. simpl. left. reflexivity.
      * subst v. simpl. right. left. reflexivity.
      * subst v. simpl. right. right. left. reflexivity.
      * subst v. simpl. right. right. right. left. reflexivity.
      * subst v. simpl. right. right. right. right. left. reflexivity.
      * simpl in Hfalse. contradiction.
Qed.