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
  Test case: input = [4; {}; []; 23.2; 9; "adasd"], output = [4; 9]
*)
Example test_case : problem_22_spec [PyInt 4; PyDict; PyList; PyFloat; PyInt 9; PyString "adasd"] [PyInt 4; PyInt 9].
Proof.
  unfold problem_22_spec.
  split.
  - apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_skip.
    apply sub_cons_match.
    apply sub_cons_skip.
    apply sub_nil.
  - intros v.
    split.
    + intros H_in.
      simpl in H_in.
      destruct H_in as [H4 | [H9 | H_false]].
      * subst. split.
        -- simpl. left. reflexivity.
        -- simpl. exact I.
      * subst. split.
        -- simpl. right. right. right. right. left. reflexivity.
        -- simpl. exact I.
      * contradiction.
    + intros [H_in H_int].
      simpl in H_in.
      destruct H_in as [H4 | [HDict | [HList | [HFloat | [H9 | [HStr | H_false]]]]]].
      * subst. simpl. left. reflexivity.
      * subst. simpl in H_int. contradiction.
      * subst. simpl in H_int. contradiction.
      * subst. simpl in H_int. contradiction.
      * subst. simpl. right. left. reflexivity.
      * subst. simpl in H_int. contradiction.
      * contradiction.
Qed.