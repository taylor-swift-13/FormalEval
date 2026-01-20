Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-1; -99; -100] (-1).
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove -1 is in the list [-1; -99; -100] *)
    simpl.
    left. reflexivity.
  - (* Part 2: Prove for all x in [-1; -99; -100], x <= -1 *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H: x = -1 \/ x = -99 \/ x = -100 \/ False *)
    destruct H as [H | [H | [H | H]]].
    + (* Case x = -1 *)
      subst. lia.
    + (* Case x = -99 *)
      subst. lia.
    + (* Case x = -100 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.