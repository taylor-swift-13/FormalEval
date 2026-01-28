Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition below_threshold_spec (l : list R) (t : R) (res : bool) : Prop :=
  (res = true <-> Forall (fun x => Rlt x t) l) /\
  (res = false <-> exists x, In x l /\ Rle t x).

Example test_below_threshold : below_threshold_spec [625/10; 16953176162073675/1000000000000000; 29851560365316985/10000000000000000] 1 false.
Proof.
  unfold below_threshold_spec.
  split.
  - split.
    + intros H. discriminate H.
    + intros H. inversion H. lra.
  - split.
    + intros _. exists (625/10). split.
      * simpl. left. reflexivity.
      * lra.
    + intros _. reflexivity.
Qed.