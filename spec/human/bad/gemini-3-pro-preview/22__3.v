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
  Test case: input = [[3; "c"; 3; 3; "a"; "b"]], output = [3; 3; 3]
*)
Example test_case : problem_22_spec 
  [PyInt 3; PyString "c"; PyInt 3; PyInt 3; PyString "a"; PyString "b"] 
  [PyInt 3; PyInt 3; PyInt 3].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: Prove is_subsequence *)
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - (* Part 2: Prove In v output <-> In v input /\ is_int v *)
    intros v.
    split.
    + (* -> Direction: In v output -> In v input /\ is_int v *)
      intros H_in.
      simpl in H_in.
      repeat match goal with
      | [ H : _ \/ _ |- _ ] => destruct H as [H | H]
      | [ H : False |- _ ] => contradiction
      end;
      rewrite <- H;
      split; [ simpl; left; reflexivity | simpl; exact I ].
    + (* <- Direction: In v input /\ is_int v -> In v output *)
      intros [H_in_input H_is_int].
      simpl in H_in_input.
      repeat match goal with
      | [ H : _ \/ _ |- _ ] => destruct H as [H | H]
      | [ H : False |- _ ] => contradiction
      end.
      * (* v = PyInt 3 *)
        rewrite <- H. simpl. left. reflexivity.
      * (* v = PyString "c" *)
        rewrite <- H in H_is_int. simpl in H_is_int. contradiction.
      * (* v = PyInt 3 *)
        rewrite <- H. simpl. left. reflexivity.
      * (* v = PyInt 3 *)
        rewrite <- H. simpl. left. reflexivity.
      * (* v = PyString "a" *)
        rewrite <- H in H_is_int. simpl in H_is_int. contradiction.
      * (* v = PyString "b" *)
        rewrite <- H in H_is_int. simpl in H_is_int. contradiction.
Qed.