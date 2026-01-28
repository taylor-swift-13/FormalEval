Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (result : bool) : Prop :=
  result = true <-> (forall x, In x l -> x < t).

Example test_below_threshold : below_threshold_spec [4%Z; -4%Z; -2%Z; 7%Z; 10%Z] 6%Z false.
Proof.
  unfold below_threshold_spec.
  split.
  - intros H. discriminate.
  - intros H.
    specialize (H 7%Z).
    simpl in H.
    assert (HIn : 4%Z = 7%Z \/ -4%Z = 7%Z \/ -2%Z = 7%Z \/ 7%Z = 7%Z \/ 10%Z = 7%Z \/ False).
    { right. right. right. left. reflexivity. }
    apply H in HIn.
    lia.
Qed.