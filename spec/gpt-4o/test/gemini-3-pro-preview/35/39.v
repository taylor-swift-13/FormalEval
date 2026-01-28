Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (max_elem : Z) : Prop :=
  In max_elem l /\ (forall x, In x l -> x <= max_elem).

Example test_max_element : max_element_spec [1; 2; 9; 4; 5; 6; -1; -1] 9.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat destruct H as [H | H]; try (subst; lia).
Qed.