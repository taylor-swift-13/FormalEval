Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [-5; 99; 2; 48; 9; 4; 6; 2; 7; 6] 99.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    right; left.
    reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; try lia | ]).
    contradiction.
Qed.