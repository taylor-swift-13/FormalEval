Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1.2%R; -4.5%R; -3.4%R; 5.6%R; 15.4%R; -8.601314347821834%R; 10.1%R] 15.4%R.
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
    + (* x = 1.2 *)
      subst. lra.
    + (* x = -4.5 *)
      subst. lra.
    + (* x = -3.4 *)
      subst. lra.
    + (* x = 5.6 *)
      subst. lra.
    + (* x = 15.4 *)
      subst. lra.
    + (* x = -8.601314347821834 *)
      subst. lra.
    + (* x = 10.1 *)
      subst. lra.
    + (* x in nil *)
      contradiction.
Qed.