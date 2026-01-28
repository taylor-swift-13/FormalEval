Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [2000000; 9000000; 8000000; 6000000; 2000001; 8000000] (-51) false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H. inversion H. lia.
  - split.
    + intros _. exists 2000000. split.
      * simpl. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.