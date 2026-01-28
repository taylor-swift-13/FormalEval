Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(*
  Modeling Python dynamic values.
*)
Inductive py_value : Type :=
  | PyInt (n : Z)          (* Integer type *)
  | PyString (s : string)    (* String type *)
  | PyFloat                  (* Float type *)
  | PyDict                   (* Dict type *)
  | PyList                   (* List type *)
  | PyNone                   (* None type *)
  | PyBool (b : bool).       (* Boolean type *)

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
  Test case: input = ["apple"; 2.71828; None; false; "watermelon"; 42; 2.71828], output = [42]
*)
Example test_case : problem_22_spec 
  [PyString "apple"; PyFloat; PyNone; PyBool false; PyString "watermelon"; PyInt 42; PyFloat] 
  [PyInt 42].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: Prove is_subsequence *)
    apply sub_cons_skip. (* skip apple *)
    apply sub_cons_skip. (* skip float *)
    apply sub_cons_skip. (* skip none *)
    apply sub_cons_skip. (* skip bool *)
    apply sub_cons_skip. (* skip watermelon *)
    apply sub_cons_match. (* match 42 *)
    apply sub_cons_skip. (* skip float *)
    apply sub_nil.
  - (* Part 2: Prove In v [42] <-> In v input /\ is_int v *)
    intros v.
    split.
    + (* -> Direction *)
      intros H_in_out.
      simpl in H_in_out.
      destruct H_in_out as [H_eq | H_false].
      * subst v.
        split.
        -- simpl. right; right; right; right; right; left; reflexivity.
        -- simpl. trivial.
      * contradiction.
    + (* <- Direction *)
      intros [H_in_input H_is_int].
      simpl in H_in_input.
      destruct H_in_input as [H_apple | [H_float1 | [H_none | [H_bool | [H_water | [H_42 | [H_float2 | H_false]]]]]]].
      * subst v. simpl in H_is_int. contradiction.
      * subst v. simpl in H_is_int. contradiction.
      * subst v. simpl in H_is_int. contradiction.
      * subst v. simpl in H_is_int. contradiction.
      * subst v. simpl in H_is_int. contradiction.
      * subst v. simpl. left. reflexivity.
      * subst v. simpl in H_is_int. contradiction.
      * contradiction.
Qed.