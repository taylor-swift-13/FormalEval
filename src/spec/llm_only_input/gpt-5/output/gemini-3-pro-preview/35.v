Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition max_element_spec (l : list Z) (res : Z) : Prop :=
  In res l /\ (forall x, In x l -> x <= res).

Example max_element_spec_test :
  max_element_spec [1%Z; 2%Z; 3%Z] 3%Z.
Proof.
  unfold max_element_spec.
  split.
  - simpl. right. right. left. reflexivity.
  - intros x Hx.
    simpl in Hx.
    destruct Hx as [Hx | [Hx | [Hx | Hx]]].
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + contradiction.
Qed.