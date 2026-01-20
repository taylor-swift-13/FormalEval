Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1; 3; 3; 5; 6; 6; 8; 8; 9; 9; 9; 10; 10; 10; 12; 12; 13; 13; 13; 13; 13; 14; 14; 15; 15; 17; 17; 18; 20; 3; 12] 20.
Proof.
  unfold max_element_spec.
  split.
  - (* Part 1: Prove 20 is in the list *)
    simpl.
    repeat (left; reflexivity || right); try contradiction.
  - (* Part 2: Prove for all x in list, x <= 20 *)
    intros x H.
    repeat (destruct H as [H | H]; [subst; lia | ]); try contradiction.
Qed.