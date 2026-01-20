Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.
Import ListNotations.

Definition max_element_spec (l : list Z) (result : Z) : Prop :=
  l <> nil /\
  In result l /\
  forall x, In x l -> x <= result.

Example max_element_spec_test_123 :
  max_element_spec [1%Z; 2%Z; 3%Z] 3%Z.
Proof.
  unfold max_element_spec.
  split.
  - discriminate.
  - split.
    + simpl. right. right. left. reflexivity.
    + intros x HIn.
      simpl in HIn.
      destruct HIn as [Hx | HIn]; [subst; lia|].
      simpl in HIn.
      destruct HIn as [Hx | HIn]; [subst; lia|].
      simpl in HIn.
      destruct HIn as [Hx | HIn]; [subst; lia|].
      contradiction.
Qed.