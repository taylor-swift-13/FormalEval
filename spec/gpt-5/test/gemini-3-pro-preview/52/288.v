Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [2000000; 10000000; 9000000; 8000000; 6000000; 8000000] 9999999 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      assert (In 10000000 [2000000; 10000000; 9000000; 8000000; 6000000; 8000000]) as HIn.
      { simpl. right. left. reflexivity. }
      rewrite Forall_forall in H.
      specialize (H _ HIn).
      lia.
  - split.
    + intros _.
      exists 10000000.
      split.
      * simpl. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.