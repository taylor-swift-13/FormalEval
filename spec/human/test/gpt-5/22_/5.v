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
  problem_22_spec [PyFloat; PyFloat; PyFloat; PyString "abc"; PyDict; PyList] [].
Proof.
  split.
  - constructor.
  - intros v; split.
    + intros H. simpl in H. contradiction.
    + intros [Hin Hinter]. simpl in Hin.
      destruct Hin as [Heq | Hin0].
      * subst v. simpl in Hinter. contradiction.
      * destruct Hin0 as [Heq | Hin1].
        { subst v. simpl in Hinter. contradiction. }
        { destruct Hin1 as [Heq | Hin2].
          { subst v. simpl in Hinter. contradiction. }
          { destruct Hin2 as [Heq | Hin3].
            { subst v. simpl in Hinter. contradiction. }
            { destruct Hin3 as [Heq | Hin4].
              { subst v. simpl in Hinter. contradiction. }
              { destruct Hin4 as [Heq | Hin5].
                { subst v. simpl in Hinter. contradiction. }
                { contradiction. } } } } }
Qed.