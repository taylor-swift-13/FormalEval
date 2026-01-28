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
    [PyInt 1%Z; PyString "2"%string; PyString "3"%string; PyInt 4%Z; PyInt (-5)%Z; PyInt 1%Z]
    [PyInt 1%Z; PyInt 4%Z; PyInt (-5)%Z; PyInt 1%Z].
Proof.
  split.
  - eapply sub_cons_match.
    eapply sub_cons_skip.
    eapply sub_cons_skip.
    eapply sub_cons_match.
    eapply sub_cons_match.
    eapply sub_cons_match.
    apply sub_nil.
  - intros v; split.
    + intros H. simpl in H.
      destruct H as [H | H].
      * subst v. split.
        { simpl. left. reflexivity. }
        { simpl. trivial. }
      * destruct H as [H | H].
        { subst v. split.
          { simpl. right. right. right. left. reflexivity. }
          { simpl. trivial. } }
        { destruct H as [H | H].
          { subst v. split.
            { simpl. right. right. right. right. left. reflexivity. }
            { simpl. trivial. } }
          { destruct H as [H | H].
            { subst v. split.
              { simpl. right. right. right. right. right. left. reflexivity. }
              { simpl. trivial. } }
            { contradiction. } } }
    + intros [Hin Hinter].
      simpl in Hin.
      destruct Hin as [H1 | Hin1].
      * subst v. simpl. left. reflexivity.
      * destruct Hin1 as [H2 | Hin2].
        { subst v. simpl in Hinter. contradiction. }
        { destruct Hin2 as [H3 | Hin3].
          { subst v. simpl in Hinter. contradiction. }
          { destruct Hin3 as [H4 | Hin4].
            { subst v. simpl. right. left. reflexivity. }
            { destruct Hin4 as [H5 | Hin5].
              { subst v. simpl. right. right. left. reflexivity. }
              { destruct Hin5 as [H6 | Hin6].
                { subst v. simpl. left. reflexivity. }
                { contradiction. } } } } }
Qed.