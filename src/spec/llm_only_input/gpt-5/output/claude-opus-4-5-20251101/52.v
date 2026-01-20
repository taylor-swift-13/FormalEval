Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example below_threshold_spec_test :
  below_threshold_spec [1%Z; 2%Z; 4%Z; 10%Z] 100%Z true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x HIn.
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn; contradiction.
  - intros _.
    reflexivity.
Qed.