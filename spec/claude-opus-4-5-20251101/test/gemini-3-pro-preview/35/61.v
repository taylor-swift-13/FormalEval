Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [2; 48; 9; 8; 6; 7] 48.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove l <> nil *)
    discriminate.
  - (* Prove In result l *)
    simpl.
    right; left.
    reflexivity.
  - (* Prove forall x, In x l -> x <= result *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]]; subst.
    + (* x = 2 *)
      lia.
    + (* x = 48 *)
      lia.
    + (* x = 9 *)
      lia.
    + (* x = 8 *)
      lia.
    + (* x = 6 *)
      lia.
    + (* x = 7 *)
      lia.
    + (* False case *)
      contradiction.
Qed.