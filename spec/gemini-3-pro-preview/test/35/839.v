Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [0; 1; 0] 1.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 1 is in the list [0; 1; 0] *)
    simpl.
    right. left. reflexivity.
  - (* Part 2: Prove for all x in [0; 1; 0], x <= 1 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | H]]].
    + (* Case x = 0 *)
      subst. lia.
    + (* Case x = 1 *)
      subst. lia.
    + (* Case x = 0 *)
      subst. lia.
    + (* Case False *)
      contradiction.
Qed.