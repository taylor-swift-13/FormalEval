Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [100; -200; -400; 500; -600] 10 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H. discriminate H.
    + intros H.
      (* Forall implies 100 < 10 which is false *)
      inversion H; subst.
      lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      exists 100.
      split.
      * simpl. left. reflexivity.
      * lia.
    + intros _. reflexivity.
Qed.