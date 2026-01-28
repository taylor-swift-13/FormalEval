Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

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

Inductive is_subsequence {A : Type} : list A -> list A -> Prop :=
  | sub_nil : forall l, is_subsequence [] l
  | sub_cons_match : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence (x :: l1) (x :: l2)
  | sub_cons_skip : forall x l1 l2, is_subsequence l1 l2 -> is_subsequence l1 (x :: l2).

Definition problem_22_pre (input : list py_value) : Prop := True.

Definition problem_22_spec (input : list py_value) (output : list py_value) : Prop :=
  is_subsequence output input /\
  (forall v, In v output <-> (In v input /\ is_int v)).

(* To deal with equality on py_value, we avoid discriminating equality (which is not decidable for all constructors).
   Instead, for this example, we carefully avoid destructing equalities on PyList. *)

Example problem_22_test1 : 
  let input := [PyList] in
  let output := [] in
  problem_22_spec input output.
Proof.
  unfold problem_22_spec.
  split.
  - (* is_subsequence [] [PyList] *)
    apply sub_nil.
  - (* forall v, In v [] <-> In v [PyList] /\ is_int v *)
    intro v.
    split.
    + (* In v [] -> ... *)
      intros H.
      inversion H.
    + (* (In v [PyList] /\ is_int v) -> In v [] *)
      intros [H_in H_int].
      (* We need to show this leads to a contradiction, since output is empty *)
      destruct H_in as [H_eq | H_nil].
      * (* v = PyList *)
        subst v.
        simpl in H_int.
        (* is_int PyList = False *)
        unfold is_int in H_int.
        simpl in H_int.
        (* by definition is_int PyList is False, so contradiction *)
        exact I.
      * contradiction.
Qed.