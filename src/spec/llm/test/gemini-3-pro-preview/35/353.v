Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-5; 16; 18; -6; -5; -5; -5; -6; 17; -5; -4; -5; -5; -5] 18.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 18 is in the list *)
    simpl.
    right. right. left. reflexivity.
  - (* Part 2: Prove for all x in list, x <= 18 *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; lia | ]).
    contradiction.
Qed.