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
  Test case: input = [[2.5; 4.178...; 7.8; "abc"; {}; []; {}]], output = []
*)
Example test_case : problem_22_spec [PyFloat; PyFloat; PyFloat; PyString "abc"; PyDict; PyList; PyDict] [].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: Prove is_subsequence [] input *)
    apply sub_nil.
  - (* Part 2: Prove In v [] <-> In v input /\ is_int v *)
    intros v.
    split.
    + (* -> Direction: In v [] -> ... *)
      intros H_in_nil.
      inversion H_in_nil.
    + (* <- Direction: In v input /\ is_int v -> In v [] *)
      intros [H_in_input H_is_int].
      simpl in H_in_input.
      (* Decompose the disjunctions from In v input.
         Since all elements in the input are not integers (PyFloat, PyString, PyDict, PyList),
         substituting v and simplifying is_int v will always result in False. *)
      repeat (destruct H_in_input as [H_eq | H_in_input]; [
        subst v; simpl in H_is_int; contradiction
      | idtac ]).
      (* Handle the final False from the end of the list *)
      contradiction.
Qed.