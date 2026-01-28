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
  | PyList                 (* List type *)
  | PyBool (b : bool)      (* Boolean type *)
  | PyNone.                (* None type *)

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
  input = [true; false; None; 0; -10; "test"; []; {}; 3.14; "test"]
  output = [0; -10]
*)
Example test_problem_22 : problem_22_spec 
  [PyBool true; PyBool false; PyNone; PyInt 0; PyInt (-10); PyString "test"; PyList; PyDict; PyFloat; PyString "test"] 
  [PyInt 0; PyInt (-10)].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: is_subsequence *)
    simpl.
    do 3 right. left. split. reflexivity.
    left. split. reflexivity.
    trivial.
  - (* Part 2: Filtering logic *)
    intros v.
    split.
    + (* Left to Right: In v output -> ... *)
      intros H.
      simpl in H.
      destruct H as [H | [H | H]]; [| | contradiction]; subst; split; simpl; auto 20; exact I.
    + (* Right to Left: In v input /\ is_int v -> ... *)
      intros [H_in H_int].
      simpl in H_in.
      repeat destruct H_in as [H_in | H_in]; subst; try (simpl in H_int; contradiction); simpl; auto.
Qed.