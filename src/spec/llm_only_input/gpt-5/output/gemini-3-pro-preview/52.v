Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example below_threshold_spec_test :
  below_threshold_spec [1%Z; 2%Z; 4%Z; 10%Z] 100%Z true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _. intros x HIn.
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    contradiction.
  - intros _. reflexivity.
Qed.