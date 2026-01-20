Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example max_element_spec_test :
  max_element_spec [-130%Z; -5%Z; -30%Z; 999991%Z; -5%Z; -5%Z; -6%Z; -6%Z; -5%Z; -5%Z; -5%Z; -6%Z] 999991%Z.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]]]; subst; lia.
Qed.