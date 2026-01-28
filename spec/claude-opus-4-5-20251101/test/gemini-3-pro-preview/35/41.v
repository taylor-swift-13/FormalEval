Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [8; 6; 6; 4; 47; 3] 47.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Prove l <> nil *)
    discriminate.
  - (* Prove In result l *)
    simpl.
    right; right; right; right; left.
    reflexivity.
  - (* Prove forall x, In x l -> x <= result *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]]; subst.
    + (* x = 8 *)
      lia.
    + (* x = 6 *)
      lia.
    + (* x = 6 *)
      lia.
    + (* x = 4 *)
      lia.
    + (* x = 47 *)
      lia.
    + (* x = 3 *)
      lia.
    + (* False case from empty list tail *)
      contradiction.
Qed.