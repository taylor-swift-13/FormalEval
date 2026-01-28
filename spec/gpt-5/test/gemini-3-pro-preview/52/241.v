Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Rlt x t) l) /\
  (res = false <-> exists x, In x l /\ Rle t x).

Example test_below_threshold : below_threshold_spec [55/10; 62/10; 8462009039856612/1000000000000000; 8565673083320917/1000000000000000] 10 true.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros _.
      repeat constructor; lra.
    + intros _.
      reflexivity.
  - split.
    + intros H.
      discriminate H.
    + intros [x [HIn HLe]].
      simpl in HIn.
      destruct HIn as [H | [H | [H | [H | H]]]]; subst; lra.
Qed.