Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < IZR t).

Example test_below_threshold :
  below_threshold_spec (6.2 :: 7.9 :: 8.1 :: 6.2 :: 6.2 :: nil) 8000001%Z true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _.
    intros x H.
    simpl in H.
    destruct H as [H | [H | [H | [H | [H | H]]]]].
    + subst x. simpl. lra.
    + subst x. simpl. lra.
    + subst x. simpl. lra.
    + subst x. simpl. lra.
    + subst x. simpl. lra.
    + contradiction.
  - intros _. reflexivity.
Qed.