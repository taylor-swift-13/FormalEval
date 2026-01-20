Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [0.2; 62.5; -63.579573934400166; 0.5; 98.82739614126038; -0.28791951724548404; -50.78504214587984; 58.062454697705476; 55.110190228263775; 10.520189946545017] 0 false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. inversion H.
  - intros H.
    specialize (H 0.2).
    assert (In 0.2 [0.2; 62.5; -63.579573934400166; 0.5; 98.82739614126038; -0.28791951724548404; -50.78504214587984; 58.062454697705476; 55.110190228263775; 10.520189946545017]).
    { simpl. left. reflexivity. }
    apply H in H0.
    lra.
Qed.