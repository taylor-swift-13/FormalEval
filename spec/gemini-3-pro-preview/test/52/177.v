Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [16.953176162073675; 2.9851560365316985] 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    (* We must prove that the condition (forall x, In x l -> x < t) is false, 
       which implies false = true is not derivable from it, but actually
       we are proving (H -> false = true). Since false = true is False,
       we need to prove ~ (forall x, ...).
       We find a counterexample in the list. *)
    specialize (H 16.953176162073675).
    assert (In 16.953176162073675 [16.953176162073675; 2.9851560365316985]) as H_in.
    { simpl. left. reflexivity. }
    apply H in H_in.
    lra.
Qed.