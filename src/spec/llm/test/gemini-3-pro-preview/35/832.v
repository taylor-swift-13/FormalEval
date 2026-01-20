Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1; 3; 3; -25; 6; 16; 7; 6; 8; 9; 9; 9; 10; 10; 10; 12; 12; 13; 13; 13; 13; 13; 14; 14; 14; 15; 15; 17; 17; 18; 19; 20] 20.
Proof.
  unfold max_element_spec.
  split.
  - simpl. do 31 right. left. reflexivity.
  - intros x H.
    repeat (destruct H as [H|H]; [subst; lia | idtac]).
    contradiction.
Qed.