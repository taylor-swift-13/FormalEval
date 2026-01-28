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
  | PyString (s : string)  (* String type *)
  | PyFloat                (* Float type *)
  | PyDict                 (* Dict type *)
  | PyList                 (* List type *)
  | PyBool (b : bool)      (* Bool type *)
  | PyNone.                (* None type *)

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
  Test case: input = [[true; false; None; 0%Z; 3.253739830287621%R; -10%Z; "test"; []; {}; 3.14%R]], output = [0%Z; -10%Z]
*)
Example test_case : problem_22_spec 
  [PyBool true; PyBool false; PyNone; PyInt 0; PyFloat; PyInt (-10); PyString "test"; PyList; PyDict; PyFloat] 
  [PyInt 0; PyInt (-10)].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: Prove is_subsequence *)
    apply sub_cons_skip. (* skip true *)
    apply sub_cons_skip. (* skip false *)
    apply sub_cons_skip. (* skip None *)
    apply sub_cons_match. (* match 0 *)
    apply sub_cons_skip. (* skip Float *)
    apply sub_cons_match. (* match -10 *)
    apply sub_cons_skip. (* skip "test" *)
    apply sub_cons_skip. (* skip [] *)
    apply sub_cons_skip. (* skip {} *)
    apply sub_cons_skip. (* skip Float *)
    apply sub_nil.
  - (* Part 2: In v output <-> In v input /\ is_int v *)
    intros v.
    split.
    + (* -> Direction: In v output -> In v input /\ is_int v *)
      intros H_in.
      simpl in H_in.
      destruct H_in as [H0 | [H10 | H_false]].
      * (* v = 0 *)
        rewrite <- H0.
        split.
        -- simpl. right; right; right; left. reflexivity.
        -- simpl. trivial.
      * (* v = -10 *)
        rewrite <- H10.
        split.
        -- simpl. right; right; right; right; right; left. reflexivity.
        -- simpl. trivial.
      * (* False *)
        contradiction.
    + (* <- Direction: In v input /\ is_int v -> In v output *)
      intros [H_in H_int].
      simpl in H_in.
      (* Decompose input list membership *)
      destruct H_in as [H_true | [H_false | [H_none | [H_0 | [H_f1 | [H_10 | [H_str | [H_list | [H_dict | [H_f2 | H_end]]]]]]]]]].
      * (* true *) rewrite <- H_true in H_int. simpl in H_int. contradiction.
      * (* false *) rewrite <- H_false in H_int. simpl in H_int. contradiction.
      * (* None *) rewrite <- H_none in H_int. simpl in H_int. contradiction.
      * (* 0 *) rewrite <- H_0. simpl. left. reflexivity.
      * (* Float *) rewrite <- H_f1 in H_int. simpl in H_int. contradiction.
      * (* -10 *) rewrite <- H_10. simpl. right. left. reflexivity.
      * (* test *) rewrite <- H_str in H_int. simpl in H_int. contradiction.
      * (* List *) rewrite <- H_list in H_int. simpl in H_int. contradiction.
      * (* Dict *) rewrite <- H_dict in H_int. simpl in H_int. contradiction.
      * (* Float *) rewrite <- H_f2 in H_int. simpl in H_int. contradiction.
      * (* End *) contradiction.
Qed.