Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

Definition max_element_spec (l : list R) (m : Z) : Prop :=
  l <> nil /\ In (IZR m) l /\ forall x, In x l -> x <= IZR m.

Example max_element_spec_test :
  max_element_spec [(3 / 2); IZR 3; IZR 2; (-7 / 2); IZR 0] 3%Z.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H|[H|[H|[H|[]]]]]; subst; lra.
Qed.