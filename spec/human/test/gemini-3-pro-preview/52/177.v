Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition problem_52_pre (l : list R) : Prop := True.

Definition problem_52_spec (l : list R) (t : R) (output : bool) : Prop :=
  (forall x, In x l -> x < t) <-> (output = true).

Example test_problem_52 : problem_52_spec [16.953176162073675; 2.9851560365316985] 1 false.
Proof.
  unfold problem_52_spec.
  split.
  - intros H.
    specialize (H 16.953176162073675).
    assert (In 16.953176162073675 [16.953176162073675; 2.9851560365316985]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
  - intros H.
    discriminate.
Qed.