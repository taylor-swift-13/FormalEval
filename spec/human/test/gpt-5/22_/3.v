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
    [PyInt 3%Z; PyString "c"; PyInt 3%Z; PyInt 3%Z; PyString "a"; PyString "b"]
    [PyInt 3%Z; PyInt 3%Z; PyInt 3%Z].
Proof.
  split.
  - eapply sub_cons_match.
    eapply sub_cons_skip.
    eapply sub_cons_match.
    eapply sub_cons_match.
    constructor.
  - intros v; split.
    + intros H.
      simpl in H.
      destruct H as [Heq | [Heq | [Heq | Hcontr]]].
      * subst v. split.
        -- simpl. left. reflexivity.
        -- simpl. exact I.
      * subst v. split.
        -- simpl. left. reflexivity.
        -- simpl. exact I.
      * subst v. split.
        -- simpl. left. reflexivity.
        -- simpl. exact I.
      * contradiction.
    + intros [Hin Hinter].
      simpl in Hin.
      destruct Hin as [Heq | Hin].
      * subst v. simpl. left. reflexivity.
      * destruct Hin as [Heq | Hin].
        -- subst v. simpl in Hinter. contradiction.
        -- destruct Hin as [Heq | Hin].
           ++ subst v. simpl. left. reflexivity.
           ++ destruct Hin as [Heq | Hin].
              ** subst v. simpl. left. reflexivity.
              ** destruct Hin as [Heq | Hin].
                 --- subst v. simpl in Hinter. contradiction.
                 --- destruct Hin as [Heq | Hin].
                     +++ subst v. simpl in Hinter. contradiction.
                     +++ contradiction.
Qed.