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

Example test_case_new : 
  problem_22_spec [PyList; PyList [PyString "arare"; PyString "world"; PyString "how"; PyString "are"; PyString "you"]] [].
Proof.
  unfold problem_22_spec.
  split.
  - simpl.
    exact I.
  - intros v.
    split.
    + intros H.
      inversion H.
    + intros [Hin His_int].
      simpl in Hin.
      destruct Hin as [H | H].
      * contradiction.
      * destruct H as [HIn | HIn].
        -- (* In v (PyList [ ... ]) *)
           inversion HIn; subst.
           discriminate.
        -- (* In v [] *)
           inversion HIn.
Qed.
Qed