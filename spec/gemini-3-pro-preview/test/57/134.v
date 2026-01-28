Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive sorted_inc : list Z -> Prop :=
  | sorted_inc_nil : sorted_inc []
  | sorted_inc_one : forall x, sorted_inc [x]
  | sorted_inc_cons : forall x y l, x <= y -> sorted_inc (y :: l) -> sorted_inc (x :: y :: l).

Inductive sorted_dec : list Z -> Prop :=
  | sorted_dec_nil : sorted_dec []
  | sorted_dec_one : forall x, sorted_dec [x]
  | sorted_dec_cons : forall x y l, x >= y -> sorted_dec (y :: l) -> sorted_dec (x :: y :: l).

Definition monotonic_spec (l : list Z) (res : bool) : Prop :=
  res = true <-> (sorted_inc l \/ sorted_dec l).

Example test_monotonic_2 : monotonic_spec [2; 2; 2; 1; -2; 1; 3; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - (* -> direction: false = true implies ... *)
    intros H. discriminate H.
  - (* <- direction: sorted implies false = true (contradiction) *)
    intros [H_inc | H_dec].
    + (* Case: sorted_inc *)
      inversion H_inc as [| | x1 y1 l1 Hle1 Hinc1]; subst. (* 2 <= 2 *)
      inversion Hinc1 as [| | x2 y2 l2 Hle2 Hinc2]; subst. (* 2 <= 2 *)
      inversion Hinc2 as [| | x3 y3 l3 Hle3 Hinc3]; subst. (* 2 <= 1 *)
      lia.
    + (* Case: sorted_dec *)
      inversion H_dec as [| | x1 y1 l1 Hge1 Hdec1]; subst. (* 2 >= 2 *)
      inversion Hdec1 as [| | x2 y2 l2 Hge2 Hdec2]; subst. (* 2 >= 2 *)
      inversion Hdec2 as [| | x3 y3 l3 Hge3 Hdec3]; subst. (* 2 >= 1 *)
      inversion Hdec3 as [| | x4 y4 l4 Hge4 Hdec4]; subst. (* 1 >= -2 *)
      inversion Hdec4 as [| | x5 y5 l5 Hge5 Hdec5]; subst. (* -2 >= 1 *)
      lia.
Qed.