Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [3; 3; 2; 2; -49; 2] 3.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 3 is in the list [3; 3; 2; 2; -49; 2] *)
    simpl.
    left. reflexivity.
  - (* Part 2: Prove for all x in [3; 3; 2; 2; -49; 2], x <= 3 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + (* Case x = 3 *)
      subst. lia.
    + (* Case x = 3 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = -49 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.