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
  | PyBool (b : bool)      (* Boolean type *)
  | PyNone                 (* None type *)
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
  input = ["apple"; 2.71828; None; false; "watermelon"; 42]
  output = [42]
*)
Example test_problem_22 : problem_22_spec 
  [PyString "apple"; PyFloat; PyNone; PyBool false; PyString "watermelon"; PyInt 42] 
  [PyInt 42].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: is_subsequence [PyInt 42] input *)
    simpl.
    (* Skip "apple" *)
    right.
    (* Skip PyFloat *)
    right.
    (* Skip PyNone *)
    right.
    (* Skip PyBool false *)
    right.
    (* Skip "watermelon" *)
    right.
    (* Match PyInt 42 *)
    left.
    split.
    + reflexivity.
    + simpl. trivial.
  - (* Part 2: forall v, In v output <-> In v input /\ is_int v *)
    intros v.
    split.
    + (* Left to Right: In v [PyInt 42] -> ... *)
      intros H.
      simpl in H.
      destruct H as [H_eq | H_false].
      * (* Case: v = PyInt 42 *)
        subst v.
        split.
        -- simpl. right. right. right. right. right. left. reflexivity.
        -- simpl. trivial.
      * (* Case: False *)
        contradiction.
    + (* Right to Left: In v input /\ is_int v -> In v [PyInt 42] *)
      intros [H_in H_int].
      simpl in H_in.
      repeat destruct H_in as [H_eq | H_in]; subst.
      * (* Case: v = "apple" *)
        simpl in H_int. contradiction.
      * (* Case: v = PyFloat *)
        simpl in H_int. contradiction.
      * (* Case: v = PyNone *)
        simpl in H_int. contradiction.
      * (* Case: v = PyBool false *)
        simpl in H_int. contradiction.
      * (* Case: v = "watermelon" *)
        simpl in H_int. contradiction.
      * (* Case: v = PyInt 42 *)
        simpl. left. reflexivity.
      * (* Case: End of list *)
        contradiction.
Qed.