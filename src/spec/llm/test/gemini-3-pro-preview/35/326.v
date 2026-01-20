Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-7; -6; -5; -5; -105; -5; -145; -5; -5; -6; -5] (-5).
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove -5 is in the list *)
    simpl.
    right. right. left. reflexivity.
  - (* Part 2: Prove for all x in list, x <= -5 *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; lia | ]).
    contradiction.
Qed.