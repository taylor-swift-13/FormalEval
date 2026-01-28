Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Import ListNotations.

(*
  Modeling Python dynamic values.
*)
Inductive py_value : Type :=
  | PyInt (n : Z)          (* Integer type *)
  | PyString (s : string)    (* String type *)
  | PyFloat                  (* Float type *)
  | PyDict                   (* Dict type *)
  | PyList.                  (* List type *)

(*
  Checker to determine if a value is an integer.
*)
Definition is_int (v : py_value) : Prop :=
  match v with
  | PyInt _ => True
  | _       => False
  end.

(*
  Subsequence definition
*)
Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

(*
  Specification Definition
*)
Definition problem_22_pre (input : list py_value) : Prop := True.

Definition problem_22_spec (input : list py_value) (output : list py_value) : Prop :=
  (* 1. Ensure output is a subsequence of input (preserves order and origin) *)
  is_subsequence output input /\
  (* 2. Core filtering logic: v is in output iff it is in input and is an integer *)
  (forall v, In v output <-> (In v input /\ is_int v)).

(*
  Example Proof
  Test case: input = [[{'1.5': ...}; true; false; None; 0%Z; -10%Z; "test"; []; {...}; 3.14%R]], output = [0%Z; -10%Z]
*)
Example test_case : problem_22_spec 
  [PyDict; PyFloat; PyFloat; PyFloat; PyInt 0%Z; PyInt (-10)%Z; PyString "test"; PyList; PyDict; PyFloat] 
  [PyInt 0%Z; PyInt (-10)%Z].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: Prove is_subsequence *)
    apply sub_cons_skip. (* PyDict *)
    apply sub_cons_skip. (* PyFloat (true) *)
    apply sub_cons_skip. (* PyFloat (false) *)
    apply sub_cons_skip. (* PyFloat (None) *)
    apply sub_cons_match. (* PyInt 0 *)
    apply sub_cons_match. (* PyInt -10 *)
    apply sub_cons_skip. (* PyString "test" *)
    apply sub_cons_skip. (* PyList *)
    apply sub_cons_skip. (* PyDict *)
    apply sub_cons_skip. (* PyFloat (3.14) *)
    apply sub_nil.
  - (* Part 2: Prove In v output <-> In v input /\ is_int v *)
    intros v.
    split.
    + (* -> Direction *)
      intros H_in.
      simpl in H_in.
      destruct H_in as [H | [H | H]].
      * subst. split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- exact I.
      * subst. split.
        -- simpl. right. right. right. right. right. left. reflexivity.
        -- exact I.
      * contradiction.
    + (* <- Direction *)
      intros [H_in H_int].
      simpl in H_in.
      destruct H_in as [H | H]; [subst; simpl in H_int; contradiction |].
      destruct H as [H | H]; [subst; simpl in H_int; contradiction |].
      destruct H as [H | H]; [subst; simpl in H_int; contradiction |].
      destruct H as [H | H]; [subst; simpl in H_int; contradiction |].
      destruct H as [H | H]; [subst; simpl; left; reflexivity |].
      destruct H as [H | H]; [subst; simpl; right; left; reflexivity |].
      destruct H as [H | H]; [subst; simpl in H_int; contradiction |].
      destruct H as [H | H]; [subst; simpl in H_int; contradiction |].
      destruct H as [H | H]; [subst; simpl in H_int; contradiction |].
      destruct H as [H | H]; [subst; simpl in H_int; contradiction |].
      contradiction.
Qed.