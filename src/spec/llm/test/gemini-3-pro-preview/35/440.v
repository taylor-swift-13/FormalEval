Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [999975; -1; 7; -1000] 999975.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 999975 is in the list [999975; -1; 7; -1000] *)
    simpl.
    left. reflexivity.
  - (* Part 2: Prove for all x in [999975; -1; 7; -1000], x <= 999975 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]].
    + (* Case x = 999975 *)
      subst. lia.
    + (* Case x = -1 *)
      subst. lia.
    + (* Case x = 7 *)
      subst. lia.
    + (* Case x = -1000 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.