Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [-34%Z; -1%Z; -5%Z; -10%Z; -15%Z; -20%Z; -25%Z; -30%Z; -35%Z; -40%Z; -45%Z; -50%Z; -55%Z; -60%Z; -65%Z; -70%Z; -75%Z; -80%Z; -85%Z; -90%Z; -95%Z; -100%Z; -105%Z; -110%Z; -115%Z; -120%Z; -125%Z; -130%Z; -135%Z; -140%Z; -145%Z; -150%Z] (-1%Z).
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|H]; [subst; lia|].
    destruct H as [H|[]]; subst; lia.
Qed.