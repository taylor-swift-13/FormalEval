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

Example problem_22_test_case_mixed_non_ints :
  problem_22_spec [PyFloat; PyFloat; PyFloat; PyString "abc"; PyDict; PyList; PyFloat] [].
Proof.
  unfold problem_22_spec.
  split.
  - simpl. exact I.
  - intro v. split.
    + intro H. simpl in H. contradiction.
    + intros [Hin Hint].
      simpl in Hin.
      destruct Hin as [Heq | Hin1].
      * subst v. simpl in Hint. contradiction.
      * simpl in Hin1.
        destruct Hin1 as [Heq1 | Hin2].
        { subst v. simpl in Hint. contradiction. }
        { simpl in Hin2.
          destruct Hin2 as [Heq2 | Hin3].
          - subst v. simpl in Hint. contradiction.
          - simpl in Hin3.
            destruct Hin3 as [Heq3 | Hin4].
            + subst v. simpl in Hint. contradiction.
            + simpl in Hin4.
              destruct Hin4 as [Heq4 | Hin5].
              * subst v. simpl in Hint. contradiction.
              * simpl in Hin5.
                destruct Hin5 as [Heq5 | Hin6].
                { subst v. simpl in Hint. contradiction. }
                { simpl in Hin6.
                  destruct Hin6 as [Heq6 | Hin7].
                  - subst v. simpl in Hint. contradiction.
                  - contradiction.
                }
        }
Qed.