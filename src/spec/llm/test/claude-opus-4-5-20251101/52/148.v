Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import Reals.
Require Import Lra.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < IZR t).

Example test_below_threshold :
  below_threshold_spec (62.5 :: 16.953176162073675 :: 2.9851560365316985 :: 16.953176162073675 :: nil) 1%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    exfalso.
    assert (In 62.5 (62.5 :: 16.953176162073675 :: 2.9851560365316985 :: 16.953176162073675 :: nil)) as Hin.
    { simpl. left. reflexivity. }
    specialize (H 62.5 Hin).
    simpl in H.
    lra.
Qed.