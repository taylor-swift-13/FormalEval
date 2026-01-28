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

Example problem_22_test_case_mixed_values_single_integer :
  problem_22_spec
    [PyString "apple";
     PyString "appaapplebcle";
     PyFloat;
     PyDict;
     PyList;
     PyString "watermelon";
     PyInt 42;
     PyFloat;
     PyString "apple"]
    [PyInt 42].
Proof.
  unfold problem_22_spec.
  split.
  - simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. left. split.
    + reflexivity.
    + simpl. exact I.
  - intro v. split.
    + intro H. simpl in H. destruct H as [Heq | Hnil]; [subst v | contradiction].
      split.
      * simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. right. simpl. left. reflexivity.
      * simpl. exact I.
    + intros [Hin Hint].
      simpl in Hin.
      destruct Hin as [Heq1 | Hin1]; [subst v; simpl in Hint; contradiction |].
      destruct Hin1 as [Heq2 | Hin2]; [subst v; simpl in Hint; contradiction |].
      destruct Hin2 as [Heq3 | Hin3]; [subst v; simpl in Hint; contradiction |].
      destruct Hin3 as [Heq4 | Hin4]; [subst v; simpl in Hint; contradiction |].
      destruct Hin4 as [Heq5 | Hin5]; [subst v; simpl in Hint; contradiction |].
      destruct Hin5 as [Heq6 | Hin6]; [subst v; simpl in Hint; contradiction |].
      destruct Hin6 as [Heq7 | Hin7]; [subst v |].
      * simpl. left. reflexivity.
      * destruct Hin7 as [Heq8 | Hin8]; [subst v; simpl in Hint; contradiction |].
        destruct Hin8 as [Heq9 | Hin9]; [subst v; simpl in Hint; contradiction |].
        simpl in Hin9. contradiction.
Qed.