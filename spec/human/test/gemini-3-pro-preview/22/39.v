Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Import ListNotations.

(*
  Modeling Python dynamic values.
  Python lists can contain different types of values. In Coq, we use an Inductive type to explicitly represent this possibility.
*)
Inductive py_value : Type :=
  | PyInt (n : Z)          (* Integer type, represented by Coq's Z *)
  | PyString (s : string)  (* String type *)
  | PyFloat                (* Float type *)
  | PyDict                 (* Dict type *)
  | PyList.                (* List type *)

(*
  Define a "checker" to determine if a value is an integer.
  is_int(v) is true if and only if v is constructed by PyInt.
*)
Definition is_int (v : py_value) : Prop :=
  match v with
  | PyInt _ => True
  | _       => False
  end.

(*
  Subsequence definition.
*)
Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

(*
  Step 4: Define the final specification Spec.
  - input: list of input values.
  - output: list of filtered integer values.
*)
Definition problem_22_pre (input : list py_value) : Prop := True.

Definition problem_22_spec (input : list py_value) (output : list py_value) : Prop :=
  (* 1. Ensure output is a subsequence of input. *)
  is_subsequence output input /\
  (* 2. Define the core filtering logic.
        A value v is in output iff it is in input and it is an integer. *)
  (forall v, In v output <-> (In v input /\ is_int v)).

(*
  Test case verification:
  input = [1.5; 1.32; 3.0; 1.5] (represented as [PyFloat; PyFloat; PyFloat; PyFloat])
  output = []
*)
Example test_problem_22 : problem_22_spec [PyFloat; PyFloat; PyFloat; PyFloat] [].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: is_subsequence *)
    simpl.
    trivial.
  - (* Part 2: forall v, In v [] <-> In v [...] /\ is_int v *)
    intros v.
    split.
    + (* Left to Right *)
      intros H.
      inversion H.
    + (* Right to Left *)
      intros [H_in H_int].
      simpl in H_in.
      (* Deconstruct the list membership. The list has 4 elements.
         The pattern matches v=e1 \/ v=e2 \/ v=e3 \/ v=e4 \/ False.
         The [] pattern at the end solves the False case immediately. *)
      destruct H_in as [H | [H | [H | [H | []]]]];
        subst v; simpl in H_int; contradiction.
Qed.