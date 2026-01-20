Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-2; -3; 0] 0.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 0 is in the list [-2; -3; 0] *)
    simpl.
    right. right. left. reflexivity.
  - (* Part 2: Prove for all x in [-2; -3; 0], x <= 0 *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H: x = -2 \/ x = -3 \/ x = 0 \/ False *)
    destruct H as [H | [H | [H | H]]].
    + (* Case x = -2 *)
      subst. lia.
    + (* Case x = -3 *)
      subst. lia.
    + (* Case x = 0 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.