Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [2; 2; 2; 1; 2; 2] 2.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 2 is in the list *)
    simpl.
    left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= 2 *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H for the list [2; 2; 2; 1; 2; 2] *)
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = 1 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case x = 2 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.