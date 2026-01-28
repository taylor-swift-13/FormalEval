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
  Test case: input = [1; "2"; "3"; 4; -5], output = [1; 4; -5]
*)
Example test_case : problem_22_spec 
  [PyInt 1%Z; PyString "2"; PyString "3"; PyInt 4%Z; PyInt (-5)%Z] 
  [PyInt 1%Z; PyInt 4%Z; PyInt (-5)%Z].
Proof.
  unfold problem_22_spec.
  split.
  - (* Part 1: Prove is_subsequence *)
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_match.
    apply sub_nil.
  - (* Part 2: Prove In v output <-> In v input /\ is_int v *)
    intros v.
    split.
    + (* -> Direction *)
      intros H_in.
      simpl in H_in.
      destruct H_in as [H1 | [H4 | [Hn5 | Hfalse]]].
      * subst v. split.
        -- simpl. left. reflexivity.
        -- simpl. trivial.
      * subst v. split.
        -- simpl. right. right. right. left. reflexivity.
        -- simpl. trivial.
      * subst v. split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- simpl. trivial.
      * contradiction.
    + (* <- Direction *)
      intros [H_in H_is_int].
      simpl in H_in.
      destruct H_in as [H1 | [H2 | [H3 | [H4 | [Hn5 | Hfalse]]]]].
      * (* v = 1 *)
        subst v. simpl. left. reflexivity.
      * (* v = "2" *)
        subst v. simpl in H_is_int. contradiction.
      * (* v = "3" *)
        subst v. simpl in H_is_int. contradiction.
      * (* v = 4 *)
        subst v. simpl. right. left. reflexivity.
      * (* v = -5 *)
        subst v. simpl. right. right. left. reflexivity.
      * contradiction.
Qed.