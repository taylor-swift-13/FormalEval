Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-1; -5; -10; 16; -15; -20; -25; -30; -35; -40; -45; -50; -55; -60; -65; -70; -75; -80; -85; -64; -90; -95; -100; -105; -110; -90; -120; -125; -130; -140; -145; -150; -80] 16.
Proof.
  unfold max_element_spec.
  split.
  - simpl.
    repeat (first [left; reflexivity | right]).
  - intros x H.
    simpl in H.
    repeat (destruct H as [H|H]; [subst; lia | ]).
    contradiction.
Qed.