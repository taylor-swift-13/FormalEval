Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

(* Pre: no special constraints for `below_threshold` *)
Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [5.5; 6.2; 7.9] (-1) false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    assert (HIn : In 5.5 [5.5; 6.2; 7.9]).
    { simpl. left. reflexivity. }
    apply H in HIn.
    lra.
  - intros H.
    discriminate.
Qed.