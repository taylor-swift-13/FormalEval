Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [100; 2000000; 300; -400; 500] (-1) false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate.
    + intros H. inversion H; subst. lia.
  - split.
    + intros _. exists 100. split.
      * simpl. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.