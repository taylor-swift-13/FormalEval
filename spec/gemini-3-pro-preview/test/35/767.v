Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-1; 999989; -1000] 999989.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 999989 is in the list [-1; 999989; -1000] *)
    simpl.
    right. left. reflexivity.
  - (* Part 2: Prove for all x in [-1; 999989; -1000], x <= 999989 *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H: x = -1 \/ x = 999989 \/ x = -1000 \/ False *)
    destruct H as [H | [H | [H | H]]].
    + (* Case x = -1 *)
      subst. lia.
    + (* Case x = 999989 *)
      subst. lia.
    + (* Case x = -1000 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.