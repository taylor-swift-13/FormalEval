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

Example test_monotonic_1 : monotonic_spec [1; 2; 9; 9; 5; 0; 0; 3] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. inversion H.
  - intros [Hinc | Hdec].
    + inversion Hinc as [| | ? ? ? Hle1 Hinc1]; subst.
      inversion Hinc1 as [| | ? ? ? Hle2 Hinc2]; subst.
      inversion Hinc2 as [| | ? ? ? Hle3 Hinc3]; subst.
      inversion Hinc3 as [| | ? ? ? Hle4 Hinc4]; subst.
      lia.
    + inversion Hdec as [| | ? ? ? Hge Hdec1]; subst.
      lia.
Qed.