Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-1; -5; -10; -15; -20; -25; -30; -35; -40; -45; -50; -55; -60; 9; -70; -75; -80; -85; -90; -95; -100; 999983; -111; -115; -120; -7; -130; -135; -140; -145; -150; -80; -130; -5; -150] 999983.
Proof.
  unfold max_element_spec.
  split.
  - simpl. repeat (first [left; reflexivity | right]).
  - intros x H.
    repeat (destruct H as [H | H]; [subst; lia | ]).
    destruct H.
Qed.