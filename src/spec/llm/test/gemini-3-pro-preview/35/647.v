Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1; 2; 3; 4; 5; 6; 18; 7; 8; 9; 9; 11; 12; 13; -145; 14; 15; 16; 17; 18; 19; 20] 20.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    repeat (try (left; reflexivity); right).
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [subst; lia | ]).
    contradiction.
Qed.