Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1.1; 3.5; 2.2; 1.1] 5 true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x HIn.
    simpl in HIn.
    destruct HIn as [H | [H | [H | [H | H]]]].
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + contradiction.
  - intros _.
    reflexivity.
Qed.