Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> [] /\
  In m l /\
  forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [-5; 2; 48; 9; 8; 6; 6; 7] 48.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    repeat (try (left; reflexivity); right).
  - intros x H.
    repeat match goal with
    | [ H : In _ (_ :: _) |- _ ] => destruct H as [H | H]; [subst; try lia | idtac]
    | [ H : In _ [] |- _ ] => contradiction
    end.
Qed.