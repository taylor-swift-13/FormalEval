Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [999992; 1; 3; 2; 1; 2; 2; 2; 1] 999992.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]];
      try (subst; lia); try contradiction.
Qed.