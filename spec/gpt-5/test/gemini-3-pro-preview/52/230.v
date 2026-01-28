Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [9; 20; 2000; 40; -50] 499 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H.
      repeat match goal with
      | h : Forall _ _ |- _ => inversion h; subst; clear h
      end.
      lia.
  - split.
    + intros _.
      exists 2000.
      split.
      * simpl. right. right. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.