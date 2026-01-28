Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [12.377301343805572; -4.430953128389664; -3.4; 5.6; 10.889126081885; 10.1] 12.377301343805572.
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
    + (* x = 12.377301343805572 *)
      subst. lra.
    + (* x = -4.430953128389664 *)
      subst. lra.
    + (* x = -3.4 *)
      subst. lra.
    + (* x = 5.6 *)
      subst. lra.
    + (* x = 10.889126081885 *)
      subst. lra.
    + (* x = 10.1 *)
      subst. lra.
    + (* x in nil *)
      contradiction.
Qed.