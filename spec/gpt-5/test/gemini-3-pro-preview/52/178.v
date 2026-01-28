Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition below_threshold_spec (l : list Z) (t : Z) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Z.lt x t) l) /\
  (res = false <-> exists x, In x l /\ Z.le t x).

Example test_below_threshold : below_threshold_spec [100; -200; 300; -400; 500; 300] 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros H.
      (* false = true is impossible *)
      discriminate H.
    + intros H.
      (* Prove that Forall (fun x => x < 1) ... is false because 100 >= 1 *)
      inversion H. lia.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros _.
      (* Witness 100 is in the list and 1 <= 100 *)
      exists 100.
      split.
      * simpl. left. reflexivity.
      * lia.
    + intros _.
      reflexivity.
Qed.