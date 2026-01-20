Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-110; -5; 21; 999973; -5] 999973.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 999973 is in the list *)
    simpl.
    right. right. right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= 999973 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + (* Case x = -110 *)
      subst. lia.
    + (* Case x = -5 *)
      subst. lia.
    + (* Case x = 21 *)
      subst. lia.
    + (* Case x = 999973 *)
      subst. lia.
    + (* Case x = -5 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.