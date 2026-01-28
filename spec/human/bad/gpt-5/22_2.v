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

Example problem_22_test_case_filter_integers :
  problem_22_spec [PyInt 4%Z; PyDict; PyList; PyFloat; PyInt 9%Z; PyString "adasd"] [PyInt 4%Z; PyInt 9%Z].
Proof.
  unfold problem_22_spec.
  split.
  - simpl. left. split. reflexivity.
    simpl. right. simpl. right. simpl. right. simpl. left. split. reflexivity.
    simpl. exact I.
  - intro v. split.
    + intro HinOut. simpl in HinOut.
      destruct HinOut as [Heq4 | HinOutTail].
      * rewrite Heq4. split.
        -- simpl. left. reflexivity.
        -- simpl. exact I.
      * simpl in HinOutTail. destruct HinOutTail as [Heq9 | HinOutTail'].
        -- rewrite Heq9. split.
           ++ simpl. right. right. right. left. reflexivity.
           ++ simpl. exact I.
        -- contradiction.
    + intros [HinIn Hint].
      simpl in HinIn.
      destruct HinIn as [Heq4 | HinRest].
      * rewrite Heq4. simpl. left. reflexivity.
      * simpl in HinRest. destruct HinRest as [HeqDict | HinRest1].
        -- rewrite HeqDict in Hint. simpl in Hint. contradiction.
        -- simpl in HinRest1. destruct HinRest1 as [HeqList | HinRest2].
           ++ rewrite HeqList in Hint. simpl in Hint. contradiction.
           ++ simpl in HinRest2. destruct HinRest2 as [HeqFloat | HinRest3].
              ** rewrite HeqFloat in Hint. simpl in Hint. contradiction.
              ** simpl in HinRest3. destruct HinRest3 as [Heq9 | HinRest4].
                 --- rewrite Heq9. simpl. right. left. reflexivity.
                 --- simpl in HinRest4. destruct HinRest4 as [HeqStr | HinRest5].
                     +++ rewrite HeqStr in Hint. simpl in Hint. contradiction.
                     +++ contradiction.
Qed.