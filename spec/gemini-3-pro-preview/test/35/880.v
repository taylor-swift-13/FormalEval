Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-5; 999978; -5; -5] 999978.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 999978 is in the list *)
    simpl.
    right. left. reflexivity.
  - (* Part 2: Prove for all x in the list, x <= 999978 *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]].
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + contradiction.
Qed.