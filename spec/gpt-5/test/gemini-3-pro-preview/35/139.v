Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [-1; -5; -10; -15; -20; -25; -30; -35; -40; -45; -104; -50; -55; -60; -65; -70; -75; -80; -85; -90; -95; -100; -105; -110; -115; -120; -125; -130; -135; -140; -145; -150; -80] (-1).
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. left. reflexivity.
  - intros x H.
    repeat (destruct H as [H|H]; [subst; lia | ]).
    contradiction.
Qed.