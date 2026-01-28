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
  Test case: input = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9], output = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]
*)
Example test_case : problem_22_spec 
  [PyInt 0%Z; PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z; PyInt 6%Z; PyInt 7%Z; PyInt 8%Z; PyInt 9%Z]
  [PyInt 0%Z; PyInt 1%Z; PyInt 2%Z; PyInt 3%Z; PyInt 4%Z; PyInt 5%Z; PyInt 6%Z; PyInt 7%Z; PyInt 8%Z; PyInt 9%Z].
Proof.
  unfold problem_22_spec.
  split.
  - repeat apply sub_cons_match.
    apply sub_nil.
  - intros v.
    split.
    + intros H_in.
      split.
      * exact H_in.
      * simpl in H_in.
        repeat destruct H_in as [<- | H_in]; simpl; auto; try contradiction.
    + intros [H_in _].
      exact H_in.
Qed.