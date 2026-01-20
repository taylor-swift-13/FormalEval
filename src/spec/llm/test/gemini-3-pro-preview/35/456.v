Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [2; 2; -49; 3; 2; 2; 2; 2] 3.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 3 is in the list *)
    simpl.
    right. right. right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= 3 *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H|H]); subst; try lia.
Qed.