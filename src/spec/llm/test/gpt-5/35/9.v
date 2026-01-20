Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.

Import ListNotations.
Open Scope Z_scope.
Open Scope R_scope.

Inductive num :=
| Z_ : Z -> num
| R_ : R -> num.

Definition toR (n : num) : R :=
  match n with
  | Z_ z => IZR z
  | R_ r => r
  end.

Definition max_element_spec (l : list num) (m : Z) : Prop :=
  l <> nil /\ In (Z_ m) l /\ forall x, In x l -> toR x <= IZR m.

Example max_element_spec_test :
  max_element_spec [R_ 1.5%R; Z_ 3%Z; Z_ 2%Z; Z_ (-4)%Z; R_ (-3.5%R); Z_ 0%Z; R_ 2.5%R] 3%Z.
Proof.
  unfold max_element_spec.
  repeat split.
  - discriminate.
  - simpl. right. left. reflexivity.
  - intros x H.
    simpl in H.
    destruct H as [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; subst; simpl; lra.
Qed.