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
  | PyList                   (* List type *)
  | PyBool (b : bool)        (* Boolean type *)
  | PyNone.                  (* None type *)

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
  Test case: input = [[true; false; None; 0%Z; -10%Z; "test"; []; {}; 3.14%R; "test"]], output = [0%Z; -10%Z]
*)
Example test_case : problem_22_spec 
  [PyBool true; PyBool false; PyNone; PyInt 0; PyInt (-10); PyString "test"; PyList; PyDict; PyFloat; PyString "test"] 
  [PyInt 0; PyInt (-10)].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: Prove is_subsequence *)
    apply sub_cons_skip. (* true *)
    apply sub_cons_skip. (* false *)
    apply sub_cons_skip. (* None *)
    apply sub_cons_match. (* 0 *)
    apply sub_cons_match. (* -10 *)
    apply sub_cons_skip. (* "test" *)
    apply sub_cons_skip. (* [] *)
    apply sub_cons_skip. (* {} *)
    apply sub_cons_skip. (* float *)
    apply sub_cons_skip. (* "test" *)
    apply sub_nil.
  - (* Part 2: Prove In v output <-> In v input /\ is_int v *)
    intros v.
    split.
    + (* -> Direction *)
      intros H_in.
      simpl in H_in.
      destruct H_in as [H0 | [H10 | H_false]].
      * (* v = 0 *)
        subst v.
        split.
        -- simpl. right. right. right. left. reflexivity.
        -- exact I.
      * (* v = -10 *)
        subst v.
        split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- exact I.
      * contradiction.
    + (* <- Direction *)
      intros [H_in H_int].
      simpl in H_in.
      repeat (destruct H_in as [H_eq | H_in]; [
        subst v; simpl in H_int; try contradiction; simpl; auto |
      ]).
      contradiction.
Qed.