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
  Test case: input = [3.0; 1.5; 1.5] (represented as [PyFloat; PyFloat; PyFloat]), output = []
*)
Example test_case : problem_22_spec [PyFloat; PyFloat; PyFloat] [].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: Prove is_subsequence [] [PyFloat; PyFloat; PyFloat] *)
    apply sub_nil.
  - (* Part 2: Prove In v [] <-> In v [PyFloat; PyFloat; PyFloat] /\ is_int v *)
    intros v.
    split.
    + (* -> Direction: In v [] -> ... *)
      intros H_in_nil.
      inversion H_in_nil.
    + (* <- Direction: In v [PyFloat; PyFloat; PyFloat] /\ is_int v -> In v [] *)
      intros [H_in_input H_is_int].
      simpl in H_in_input.
      (* Decompose the disjunctions from the list membership *)
      destruct H_in_input as [H_eq | [H_eq | [H_eq | H_false]]].
      * (* v is the first PyFloat *)
        subst v.
        simpl in H_is_int.
        contradiction.
      * (* v is the second PyFloat *)
        subst v.
        simpl in H_is_int.
        contradiction.
      * (* v is the third PyFloat *)
        subst v.
        simpl in H_is_int.
        contradiction.
      * (* End of list *)
        contradiction.
Qed.