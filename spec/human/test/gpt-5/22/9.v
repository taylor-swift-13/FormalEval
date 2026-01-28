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

Example problem_22_test_case_input_list_of_mixed_values :
  problem_22_spec
    [PyString "apple"; PyFloat; PyDict; PyList; PyString "watermelon"; PyInt 42%Z]
    [PyInt 42%Z].
Proof.
  unfold problem_22_spec.
  split.
  - simpl.
    right. simpl.
    right. simpl.
    right. simpl.
    right. simpl.
    right. simpl.
    left. split.
    + reflexivity.
    + simpl. exact I.
  - intro v. split.
    + intro H. simpl in H. destruct H as [Heq | Hfalse].
      * subst v. split.
        -- simpl. right. right. right. right. right. left. reflexivity.
        -- simpl. exact I.
      * contradiction.
    + intros [Hin Hint].
      simpl in Hin.
      destruct Hin as [Happle | Hin1].
      * subst v. simpl in Hint. contradiction.
      * destruct Hin1 as [Hfloat | Hin2].
        -- subst v. simpl in Hint. contradiction.
        -- destruct Hin2 as [Hdict | Hin3].
           ++ subst v. simpl in Hint. contradiction.
           ++ destruct Hin3 as [Hlist | Hin4].
              ** subst v. simpl in Hint. contradiction.
              ** destruct Hin4 as [Hwatermelon | Hin5].
                 --- subst v. simpl in Hint. contradiction.
                 --- destruct Hin5 as [H42 | HinEmpty].
                     +++ subst v. simpl. left. reflexivity.
                     +++ simpl in HinEmpty. contradiction.
Qed.