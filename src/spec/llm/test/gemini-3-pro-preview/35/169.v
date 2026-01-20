Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1; 3; 3; 5; 6; 6; 6; 8; 8; 9; 9; 9; 9; 10; 10; 12; 12; 13; 13; 13; 13; 13; 14; 15; 15; 17; 17; 18; 19; 999976; 3; 3] 999976.
Proof.
  unfold max_element_spec.
  split.
  - repeat (try (left; reflexivity); right).
  - intros x H.
    repeat (destruct H as [H|H]; [subst; lia | ]).
    contradiction.
Qed.