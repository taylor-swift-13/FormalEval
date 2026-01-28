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
    [PyDict; PyList; PyList; PyList; PyInt (0%Z); PyInt (-10%Z); PyString "test"; PyList; PyDict; PyFloat]
    [PyInt (0%Z); PyInt (-10%Z)].
Proof.
  split.
  - apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - intros v; split.
    + intros H. simpl in H. destruct H as [Heq | Hrest].
      * subst v. split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- simpl. trivial.
      * destruct Hrest as [Heq | Hrest0].
        -- subst v. split.
           ++ simpl. right. right. right. right. right. left. reflexivity.
           ++ simpl. trivial.
        -- simpl in Hrest0. contradiction.
    + intros [Hin Hinter]. simpl in Hin.
      destruct Hin as [Heq | Hin0].
      * subst v. simpl in Hinter. contradiction.
      * destruct Hin0 as [Heq | Hin1].
        -- subst v. simpl in Hinter. contradiction.
        -- destruct Hin1 as [Heq | Hin2].
           ++ subst v. simpl in Hinter. contradiction.
           ++ destruct Hin2 as [Heq | Hin3].
              ** subst v. simpl in Hinter. contradiction.
              ** destruct Hin3 as [Heq | Hin4].
                 --- subst v. left. reflexivity.
                 --- destruct Hin4 as [Heq | Hin5].
                     +++ subst v. right. left. reflexivity.
                     +++ destruct Hin5 as [Heq | Hin6].
                         *** subst v. simpl in Hinter. contradiction.
                         *** destruct Hin6 as [Heq | Hin7].
                             **** subst v. simpl in Hinter. contradiction.
                             **** destruct Hin7 as [Heq | Hin8].
                                  ***** subst v. simpl in Hinter. contradiction.
                                  ***** destruct Hin8 as [Heq | Hin9].
                                        ------ subst v. simpl in Hinter. contradiction.
                                        ------ simpl in Hin9. contradiction.
Qed.