Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (m : Z) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [100; 100; 99; 98; 97; 96] 100.
Proof.
  unfold max_element_spec.
  repeat split.
  - (* Case 1: l <> nil *)
    discriminate.
  - (* Case 2: In m l *)
    simpl.
    left. reflexivity.
  - (* Case 3: forall x, In x l -> x <= m *)
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | [H | H]]]]]].
    + (* x = 100 *)
      subst. lia.
    + (* x = 100 *)
      subst. lia.
    + (* x = 99 *)
      subst. lia.
    + (* x = 98 *)
      subst. lia.
    + (* x = 97 *)
      subst. lia.
    + (* x = 96 *)
      subst. lia.
    + (* x in nil *)
      contradiction.
Qed.