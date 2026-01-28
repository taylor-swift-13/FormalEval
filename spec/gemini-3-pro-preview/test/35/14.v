Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [101] 101.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 101 is in the list [101] *)
    simpl.
    left. reflexivity.
  - (* Part 2: Prove for all x in [101], x <= 101 *)
    intros x H.
    simpl in H.
    destruct H as [H | H].
    + (* Case x = 101 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.