Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < IZR t).

Example test_below_threshold :
  below_threshold_spec (6.576799211228067 :: 5.5 :: 5.50048632089892 :: 6.2212876393256 :: 7.9 :: nil) 300%Z true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _.
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + subst x. lra.
    + contradiction.
  - intros _. reflexivity.
Qed.