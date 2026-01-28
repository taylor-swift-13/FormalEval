Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example test_max_element : max_element_spec [-5; 9; 4; 5; 7; 9] 9.
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
    + (* x = -5 *)
      lia.
    + (* x = 9 *)
      lia.
    + (* x = 4 *)
      lia.
    + (* x = 5 *)
      lia.
    + (* x = 7 *)
      lia.
    + (* x = 9 *)
      lia.
    + (* False case from empty list tail *)
      contradiction.
Qed.