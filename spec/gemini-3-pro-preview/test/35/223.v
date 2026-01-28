Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [1; 3; 3; 5; 6; 6; 6; 8; 8; 9; 9; 9; 9; 10; 10; 10; 12; 12; 13; 13; 13; 13; -100; 13; 14; 14; 15; 15; 3; 17; 17; 18; 19; -95; 20; -1; 3] 20.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    repeat (match goal with
            | [ |- ?X = ?X \/ _ ] => left; reflexivity
            | [ |- ?X = ?X ] => reflexivity
            | [ |- _ \/ _ ] => right
            end).
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lia | ]).
    contradiction.
Qed.