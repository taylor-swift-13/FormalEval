Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [1000; 500; 250; 6000000; 62; 31] 2000 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      assert (In 6000000 [1000; 500; 250; 6000000; 62; 31]).
      { simpl. right. right. right. left. reflexivity. }
      rewrite Forall_forall in H.
      specialize (H _ H0).
      lia.
  - split.
    + intros _.
      exists 6000000.
      split.
      * simpl. right. right. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.