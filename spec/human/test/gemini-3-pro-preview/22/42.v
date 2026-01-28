Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Import ListNotations.
Open Scope string_scope.

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
  input = [true; false; None; 0; -10; "test"; []; {}; 3.14; None]
  output = [0; -10]
*)
Example test_problem_22 : problem_22_spec 
  [PyBool true; PyBool false; PyNone; PyInt 0%Z; PyInt (-10)%Z; PyString "test"; PyList; PyDict; PyFloat; PyNone] 
  [PyInt 0%Z; PyInt (-10)%Z].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: is_subsequence *)
    right. right. right. (* Skip true, false, None *)
    left. split; [reflexivity | ]. (* Match 0 *)
    left. split; [reflexivity | ]. (* Match -10 *)
    simpl. trivial.
  - (* Part 2: forall v, In v output <-> In v input /\ is_int v *)
    intros v.
    split.
    + (* Left to Right: In v output -> In v input /\ is_int v *)
      intros H.
      simpl in H.
      destruct H as [H0 | [Hn10 | Hfalse]].
      * (* v = 0 *)
        subst v. split.
        { simpl. right. right. right. left. reflexivity. }
        { simpl. trivial. }
      * (* v = -10 *)
        subst v. split.
        { simpl. right. right. right. right. left. reflexivity. }
        { simpl. trivial. }
      * contradiction.
    + (* Right to Left: In v input /\ is_int v -> In v output *)
      intros [Hin Hint].
      simpl in Hin.
      repeat destruct Hin as [Heq | Hin];
        try (subst v; simpl in Hint; try contradiction; simpl; auto).
      contradiction.
Qed.