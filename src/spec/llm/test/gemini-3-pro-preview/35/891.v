Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [4.977938453667969%R; 1.2%R; -4.5%R; -3.4%R; 5.6%R; 7.8%R; -9.0%R; 10.1%R; -12.3%R; -25.6%R; -68.11296101258709%R; -35.8%R; 40.9%R; -46.0%R; 51.1%R; 57.2%R; -63.3%R; 69.4%R; -75.5%R; -87.7%R; 93.8%R; 99.9%R; -4.5%R] 99.9%R.
Proof.
  unfold max_element_spec.
  split.
  - repeat (first [left; reflexivity | right]).
  - intros x H.
    repeat (destruct H as [H|H]; [subst; lra | ]).
    contradiction.
Qed.