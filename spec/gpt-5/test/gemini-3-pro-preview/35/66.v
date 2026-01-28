Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [8; 6; 6; 6; 47; 46; 3] 47.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Case 1: l <> nil *)
    discriminate.
  - (* Case 2: In m l *)
    simpl.
    right. right. right. right. left. reflexivity.
  - (* Case 3: forall x, In x l -> x <= m *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | [H | H]]]]]]].
    + (* x = 8 *)
      subst. lia.
    + (* x = 6 *)
      subst. lia.
    + (* x = 6 *)
      subst. lia.
    + (* x = 6 *)
      subst. lia.
    + (* x = 47 *)
      subst. lia.
    + (* x = 46 *)
      subst. lia.
    + (* x = 3 *)
      subst. lia.
    + (* x in nil *)
      contradiction.
Qed.