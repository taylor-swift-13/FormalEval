Require Import List.
Require Import ZArith.
Require Import Reals.
Require Import Lia.
Require Import Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold :
  below_threshold_spec (1.430414675639685 :: 6.2 :: 7.9 :: 0.32055210364227493 :: nil) 300 true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _.
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | H]]]].
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + contradiction.
  - intros _. reflexivity.
Qed.