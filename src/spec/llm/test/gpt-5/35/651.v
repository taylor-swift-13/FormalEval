Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 18%Z; -20%Z; 8%Z; 999990%Z; 9%Z; 11%Z; 12%Z; 13%Z; -145%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z] 999990%Z.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. right. right. right. right. right. right. right. right. left. reflexivity.
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
    destruct H as [H|[]]; subst; lia.
Qed.