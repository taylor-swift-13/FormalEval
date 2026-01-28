Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition monotonic_spec (l : list R) (result : bool) : Prop :=
  result = true <-> 
    (forall i j, (i < j < length l)%nat -> nth i l 0 <= nth j l 0) \/
    (forall i j, (i < j < length l)%nat -> nth i l 0 >= nth j l 0).

Example test_monotonic_real : monotonic_spec [65.42404804168314%R; -27.467401242304092%R; 1.1695217804835494%R; -88.22454119231631%R; -43.03246997899461%R; 6.289214420714728%R; 62.246881897996445%R; -27.613728995144186%R; -89.64771597158368%R; 91.94959500461121%R] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + specialize (Hinc 0%nat 1%nat).
      simpl in Hinc.
      assert (H : (0 < 1 < 10)%nat) by lia.
      apply Hinc in H.
      lra.
    + specialize (Hdec 1%nat 2%nat).
      simpl in Hdec.
      assert (H : (1 < 2 < 10)%nat) by lia.
      apply Hdec in H.
      lra.
Qed.