Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition b2z (b : bool) : Z := if b then 1 else 0.

Inductive sorted_inc : list bool -> Prop :=
  | sorted_inc_nil : sorted_inc []
  | sorted_inc_one : forall x, sorted_inc [x]
  | sorted_inc_cons : forall x y l, b2z x <= b2z y -> sorted_inc (y :: l) -> sorted_inc (x :: y :: l).

Inductive sorted_dec : list bool -> Prop :=
  | sorted_dec_nil : sorted_dec []
  | sorted_dec_one : forall x, sorted_dec [x]
  | sorted_dec_cons : forall x y l, b2z x >= b2z y -> sorted_dec (y :: l) -> sorted_dec (x :: y :: l).

Definition monotonic_spec (l : list bool) (res : bool) : Prop :=
  res = true <-> (sorted_inc l \/ sorted_dec l).

Example test_monotonic_1 : monotonic_spec [false; true; false; false; true; true; true; true] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [H | H].
    + (* sorted_inc case *)
      inversion H; subst.
      (* The first pair (false, true) is increasing (0 <= 1), so we check the tail *)
      match goal with H: sorted_inc _ |- _ => inversion H; subst end.
      (* The second pair (true, false) is not increasing (1 <= 0 is false) *)
      simpl in *. lia.
    + (* sorted_dec case *)
      inversion H; subst.
      (* The first pair (false, true) is not decreasing (0 >= 1 is false) *)
      simpl in *. lia.
Qed.