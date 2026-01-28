Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [2; 1; 3; 2; 2; 3; 2; 2] 3.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat destruct H as [H | H]; try (subst; lia); try contradiction.
Qed.