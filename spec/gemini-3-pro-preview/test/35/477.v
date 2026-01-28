Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-130; -5; -30; 999991; -5; -5; -6; -6; -5; -5; -5; -6] 999991.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    right. right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat match goal with
           | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
           | [ H : _ = _ |- _ ] => subst; try lia
           | [ H : False |- _ ] => contradiction
           end.
Qed.