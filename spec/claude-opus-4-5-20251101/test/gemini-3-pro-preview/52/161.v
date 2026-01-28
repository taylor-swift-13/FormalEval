Require Import List.
Require Import Reals.
Require Import Lra.
Import ListNotations.

Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [1000; 500; 126; 250; 125; 625/10; 3125/100; 3125/100; 500] 2000 true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x HIn.
    simpl in HIn.
    repeat (destruct HIn as [H | HIn]; [subst; lra | ]).
    contradiction.
  - intros _.
    reflexivity.
Qed.