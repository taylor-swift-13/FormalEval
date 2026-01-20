Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [3; 2; 2; 2; 2; 5] 5.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 5 is in the list [3; 2; 2; 2; 2; 5] *)
    simpl.
    right. right. right. right. right. left. reflexivity.
  - (* Part 2: Prove for all x in [3; 2; 2; 2; 2; 5], x <= 5 *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H *)
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + (* Case x = 3 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = 5 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.