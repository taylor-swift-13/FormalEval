Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Import ListNotations.

Inductive py_value : Type :=
  | PyInt (n : Z)
  | PyString (s : string)
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

Example test_case_empty_list : 
  problem_22_spec [PyList] [].
Proof.
  unfold problem_22_spec.
  split.
  - (* Prove is_subsequence [] [PyList] *)
    simpl.
    exact I.
  - (* Prove forall v, In v [] <-> (In v [PyList] /\ is_int v) *)
    intros v.
    split.
    + (* Forward direction: In v [] -> ... *)
      intros H.
      inversion H.  (* In v [] is always false *)
    + (* Backward direction: (In v [PyList] /\ is_int v) -> In v [] *)
      intros [Hin His_int].
      simpl in Hin.
      destruct Hin as [H | H].
      * (* Case v = PyList *)
        subst v.
        simpl in His_int.
        contradiction.
      * (* Case H: In v [] *)
        inversion H.
Qed.