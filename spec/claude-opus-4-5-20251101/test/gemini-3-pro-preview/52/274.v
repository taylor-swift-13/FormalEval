Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [2000000%Z; 501%Z; 10000000%Z; 9000000%Z; 8000000%Z; 6000000%Z; 2000000%Z; 8000000%Z; 8000000%Z] 10000001%Z true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x HIn.
    simpl in HIn.
    repeat (destruct HIn as [H | HIn]; [subst; lia | idtac]).
    contradiction.
  - intros _.
    reflexivity.
Qed.