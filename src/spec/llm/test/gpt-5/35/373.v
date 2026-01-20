Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [-5%Z; -7%Z; -5%Z; -5%Z; -5%Z; -5%Z; -4%Z; -7%Z; -145%Z; -5%Z; -5%Z; -6%Z; -5%Z] (-4%Z).
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. right. right. right. right. right. left. reflexivity.
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
    destruct H as [H|[]]; subst; lia.
Qed.