Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

(* For string_dec *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Open Scope string_scope.

Inductive py_value : Type :=
  | PyInt (n : Z)          (* 整数类型，我们用 Coq 的 Z 来表示 *)
  | PyString (s : string)  (* 字符串类型 *)
  | PyFloat
  | PyDict
  | PyList.

Definition is_int (v : py_value) : Prop :=
  match v with
  | PyInt _ => True
  | _       => False
  end.

Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

Definition problem_22_pre (input : list py_value) : Prop := True.

Definition problem_22_spec (input : list py_value) (output : list py_value) : Prop :=
  is_subsequence output input /\
  (forall v, In v output <-> (In v input /\ is_int v)).

Example problem_22_test1 :
  problem_22_spec [PyList] [].
Proof.
  unfold problem_22_spec.
  split.
  - (* is_subsequence [] [PyList] = True *)
    simpl. exact I.
  - intros v; split.
    + intros H. inversion H.  (* In v [] is false *)
    + intros [H_in H_int].
      simpl in H_in.
      destruct H_in as [H_eq | H_in_false].
      * subst v.
        (* Contradiction: is_int PyList is False *)
        unfold is_int in H_int.
        (* is_int PyList = False *)
        (* so H_int is False; contradiction *)
        exact I.
      * contradiction.
Qed.