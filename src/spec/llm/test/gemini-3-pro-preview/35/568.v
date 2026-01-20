Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example test_max_element : max_element_spec [999970; 2; 1; 4; 2; 2; 1; 1; 2; 2; 2; 3; 3] 999970.
Proof.
  unfold max_element_spec.
  split.
  - simpl. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lia | ]).
    contradiction.
Qed.