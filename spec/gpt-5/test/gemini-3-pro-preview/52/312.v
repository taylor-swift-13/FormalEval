Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [100; 9999999; -400; 19] 8000000 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      inversion H; subst.
      inversion H3; subst.
      lia.
  - split.
    + intros _.
      exists 9999999.
      split.
      * simpl. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.