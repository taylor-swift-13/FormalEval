Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : R) : Prop :=
  l <> nil /\ In m l /\ forall x, In x l -> x <= m.

Example test_max_element : max_element_spec [1.2%R; -4.5%R; -46.0%R; 17.742268880987826%R; 11.01793702200241%R; 7.8%R; -9.0%R; 10.1%R; 10.1%R; 10.1%R] 17.742268880987826%R.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl.
    right. right. right. left. reflexivity.
  - intros x H.
    simpl in H.
    repeat (destruct H as [H | H]; [subst; lra | ]).
    contradiction.
Qed.