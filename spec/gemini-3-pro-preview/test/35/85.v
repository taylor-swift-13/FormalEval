Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [97; 100; 100; 100; 100] 100.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 100 is in the list *)
    simpl.
    right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= 100 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + (* Case x = 97 *)
      subst. lia.
    + (* Case x = 100 *)
      subst. lia.
    + (* Case x = 100 *)
      subst. lia.
    + (* Case x = 100 *)
      subst. lia.
    + (* Case x = 100 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.