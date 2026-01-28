Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [8; 6; 6; 4; 3; 98; 3; 8] 98.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove l <> nil *)
    discriminate.
  - (* Prove In result l *)
    simpl.
    right; right; right; right; right; left.
    reflexivity.
  - (* Prove forall x, In x l -> x <= result *)
    intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lia | ]).
    contradiction.
Qed.