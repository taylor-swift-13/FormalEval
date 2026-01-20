Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [999988; 1; 2; 3; 4; 5; 7; 8; 999992; 10; 21; 13; 4; 14; 15; 17; 999976; 19; 20; 999991; 11] 999992.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    repeat ((left; reflexivity) || right).
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [subst; lia | ]).
    contradiction.
Qed.