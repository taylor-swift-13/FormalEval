Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1; 2; 3; 4; 12; 5; 6; 18; 7; 8; 9; 9; 11; 12; 13; -145; 14; 15; 16; 17; 18; 19; 19; 9] 19.
Proof.
  unfold max_element_spec.
  split.
  - simpl. repeat (first [left; reflexivity | right]).
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [subst; try lia | ]).
    contradiction.
Qed.