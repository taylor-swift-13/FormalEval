Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Rlt x t) l) /\
  (res = false <-> exists x, In x l /\ Rle t x).

Example test_below_threshold : below_threshold_spec [1000; 500; 250; 62.5; 30.807804019985152; -50.78504214587984; 62.5] 2000 true.
Proof.
  unfold below_threshold_spec.
  split.
  - (* Case: res = true <-> Forall ... *)
    split.
    + intros _.
      (* Prove that all elements in the list are < 2000 *)
      repeat constructor; lra.
    + intros _.
      reflexivity.
  - (* Case: res = false <-> exists ... *)
    split.
    + intros H.
      (* true = false is impossible *)
      discriminate H.
    + intros [x [HIn HLe]].
      (* Prove that no element in the list is >= 2000 *)
      simpl in HIn.
      destruct HIn as [H | [H | [H | [H | [H | [H | [H | H]]]]]]]; subst; lra.
Qed.