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
    [PyInt 0%Z; PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z; PyInt 6%Z; PyInt 7%Z; PyInt 8%Z; PyInt 9%Z]
    [PyInt 0%Z; PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z; PyInt 6%Z; PyInt 7%Z; PyInt 8%Z; PyInt 9%Z].
Proof.
  split.
  - apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_cons_match.
    constructor.
  - intros v; split.
    + intros Hin. split.
      * exact Hin.
      * simpl in Hin.
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        destruct Hin as [Heq | Hin]; [subst; simpl; trivial |].
        simpl in Hin. contradiction.
    + intros [Hin Hinter]. exact Hin.
Qed.