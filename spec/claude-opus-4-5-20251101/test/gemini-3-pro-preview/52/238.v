Require Import List.
Require Import ZArith.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < IZR t).

Example test_below_threshold : below_threshold_spec [5.5%R; 2.8%R; 8.1%R] 7000001%Z true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x HIn.
    simpl in HIn.
    destruct HIn as [H | [H | [H | H]]].
    + subst. lra.
    + subst. lra.
    + subst. lra.
    + contradiction.
  - intros _. reflexivity.
Qed.