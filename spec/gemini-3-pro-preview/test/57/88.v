Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Inductive sorted_inc : list R -> Prop :=
  | sorted_inc_nil : sorted_inc []
  | sorted_inc_one : forall x, sorted_inc [x]
  | sorted_inc_cons : forall x y l, x <= y -> sorted_inc (y :: l) -> sorted_inc (x :: y :: l).

Inductive sorted_dec : list R -> Prop :=
  | sorted_dec_nil : sorted_dec []
  | sorted_dec_one : forall x, sorted_dec [x]
  | sorted_dec_cons : forall x y l, x >= y -> sorted_dec (y :: l) -> sorted_dec (x :: y :: l).

Definition monotonic_spec (l : list R) (res : bool) : Prop :=
  res = true <-> (sorted_inc l \/ sorted_dec l).

Example test_monotonic_1 : monotonic_spec [65.42404804168314%R; -27.467401242304092%R; 1.1695217804835494%R; -88.22454119231631%R; -43.03246997899461%R; 6.289214420714728%R; 62.246881897996445%R; -27.613728995144186%R; -89.64771597158368%R; 91.94959500461121%R] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [Hinc | Hdec].
    + inversion Hinc; subst.
      lra.
    + inversion Hdec; subst.
      match goal with H: sorted_dec _ |- _ => inversion H; subst end.
      lra.
Qed.