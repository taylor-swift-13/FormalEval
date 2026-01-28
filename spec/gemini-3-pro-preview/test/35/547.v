Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (res : R) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1.2%R; -4.5%R; -3.4%R; 5.6%R; 7.8%R; -9.0%R; 10.1%R; -12.3%R; 15.4%R; 20.5%R; -25.6%R; 30.7%R; -35.8%R; 40.9%R; -46.0%R; -8.601314347821834%R; 57.2%R; -63.3%R; 69.4%R; -75.5%R; 81.6%R; -87.7%R; 77.07852302260174%R; 99.9%R; 10.1%R] 99.9%R.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    repeat (try (left; reflexivity); right).
  - intros x H.
    simpl in H.
    repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H as [H | H]; [ subst; lra | ]
    | [ H : False |- _ ] => contradiction
    end.
Qed.