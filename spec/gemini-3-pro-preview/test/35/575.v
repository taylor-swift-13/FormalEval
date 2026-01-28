Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [-5%Z; -70%Z; -15%Z; -20%Z; -25%Z; -30%Z; 11%Z; -35%Z; -40%Z; -45%Z; -104%Z; -50%Z; -55%Z; -60%Z; -65%Z; -105%Z; -75%Z; -80%Z; -85%Z; -90%Z; -95%Z; -100%Z; 8%Z; -105%Z; -110%Z; -115%Z; -120%Z; -125%Z; -130%Z; -135%Z; -140%Z; -145%Z; -150%Z; -80%Z; -5%Z; -95%Z] 11%Z.
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