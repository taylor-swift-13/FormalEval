Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-5; 17; -6; -5; -5; -5; -6; 17; -5; -5; -5; -5] 17.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H; try (subst; lia)).
Qed.