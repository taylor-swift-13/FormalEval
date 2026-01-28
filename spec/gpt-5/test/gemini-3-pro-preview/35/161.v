Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [-5; -6; -5; -5; -5; -5; -5; -145; -5; -4; -5; -6] (-4).
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    do 9 right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [ subst; try lia | ]).
    contradiction.
Qed.