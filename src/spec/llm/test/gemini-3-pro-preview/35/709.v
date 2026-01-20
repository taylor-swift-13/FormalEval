Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [19; 999974] 999974.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 999974 is in the list [19; 999974] *)
    simpl.
    right. left. reflexivity.
  - (* Part 2: Prove for all x in [19; 999974], x <= 999974 *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H: x = 19 \/ x = 999974 \/ False *)
    destruct H as [H | [H | H]].
    + (* Case x = 19 *)
      subst. lia.
    + (* Case x = 999974 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.