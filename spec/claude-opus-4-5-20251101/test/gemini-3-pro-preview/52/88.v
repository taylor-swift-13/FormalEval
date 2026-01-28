Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [-2%Z; -3%Z; -3%Z; -4%Z] 0%Z true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x HIn.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | H]]]].
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + contradiction.
  - intros _.
    reflexivity.
Qed.