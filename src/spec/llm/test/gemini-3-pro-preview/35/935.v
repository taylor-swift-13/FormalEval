Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1; 2; 3; 4; 5; 999977; 7; 8; -2; 10; 21; 12; 13; 14; 15; 16; 17; 999976; 19; 20; 15; 11] 999977.
Proof.
  unfold max_element_spec.
  split.
  - simpl. do 5 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lia | ]).
    contradiction.
Qed.