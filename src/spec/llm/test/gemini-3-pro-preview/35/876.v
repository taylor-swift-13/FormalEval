Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1; 3; 3; -25; 6; 6; 6; 8; 8; 9; 9; 9; 9; 10; 10; 13; 10; 12; 12; 13; 13; 13; 13; 13; 999993; 14; 15; 15; -125; 15; 17; 17; 18; 19; 20; 15; 9] 999993.
Proof.
  unfold max_element_spec.
  split.
  - simpl. repeat (first [ left; reflexivity | right ]).
  - intros x H. simpl in H.
    repeat (destruct H as [H|H]; [subst; lia | ]).
    contradiction.
Qed.