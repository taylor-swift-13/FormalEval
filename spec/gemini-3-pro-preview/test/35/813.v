Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-5; 999978; -5] 999978.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 999978 is in the list [-5; 999978; -5] *)
    simpl.
    right. left. reflexivity.
  - (* Part 2: Prove for all x in [-5; 999978; -5], x <= 999978 *)
    intros x H.
    simpl in H.
    (* Break down the hypothesis H: x = -5 \/ x = 999978 \/ x = -5 \/ False *)
    destruct H as [H | [H | [H | H]]].
    + (* Case x = -5 *)
      subst. lia.
    + (* Case x = 999978 *)
      subst. lia.
    + (* Case x = -5 *)
      subst. lia.
    + (* Case False (end of list) *)
      contradiction.
Qed.