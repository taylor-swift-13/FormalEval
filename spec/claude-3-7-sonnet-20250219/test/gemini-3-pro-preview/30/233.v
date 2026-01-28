Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition get_positive_spec (l: list Z) (res: list Z) : Prop :=
  (forall x, In x res -> In x l /\ x > 0) /\
  (forall x, In x l -> x > 0 -> In x res).

Example test_get_positive : get_positive_spec [1; 2; -4; -5; 0; 2; 6; 7; -9; 7] [1; 2; 2; 6; 7; 7].
Proof.
  unfold get_positive_spec.
  split.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [| try contradiction]); subst; split; try (simpl; tauto); try lia.
  - intros x HIn HPos.
    simpl in HIn.
    repeat (destruct HIn as [HIn | HIn]; [| try contradiction]); subst; try (simpl; tauto); try lia.
Qed.