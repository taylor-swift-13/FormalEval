Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  res = true <-> (forall x, In x l -> x < t).

Example test_below_threshold: below_threshold_spec [8000001; 9999998; 9000000; 10; 9999999; 8000000; 7000000; 6000000; 2000000] 10000001 true.
Proof.
  unfold below_threshold_spec.
  split.
  - intros _ x H.
    simpl in H.
    repeat (destruct H as [H|H]; [subst; lia|]).
    contradiction.
  - intros _.
    reflexivity.
Qed.