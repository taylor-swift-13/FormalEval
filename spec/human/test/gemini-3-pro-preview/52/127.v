Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [62.5; 16.953176162073675; 2.9851560365316985] 1 false.
Proof.
  unfold problem_52_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    (* The hypothesis H implies that every element is < 1. 
       We show a contradiction by picking 62.5 which is >= 1. *)
    assert (HIn : In 62.5 [62.5; 16.953176162073675; 2.9851560365316985]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    lra.
  - (* Right to Left implication *)
    intros H.
    (* H is false = true, which is a contradiction *)
    discriminate.
Qed.