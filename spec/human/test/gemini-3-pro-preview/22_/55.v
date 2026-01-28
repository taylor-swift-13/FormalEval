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
  Test case: input = [4.6; 7.8; 3.14; "aapplebc"; {}; 5.27...; []; 2.5; 7.8], output = []
*)
Example test_case : problem_22_spec 
  [PyFloat; PyFloat; PyFloat; PyString "aapplebc"; PyDict; PyFloat; PyList; PyFloat; PyFloat] 
  [].
Proof.
  unfold problem_22_spec.
  split.
  - apply sub_nil.
  - intros v.
    split.
    + intros H_in_nil.
      inversion H_in_nil.
    + intros [H_in_input H_is_int].
      simpl in H_in_input.
      repeat destruct H_in_input as [H_eq | H_in_input];
        try (subst; simpl in H_is_int; contradiction).
Qed.