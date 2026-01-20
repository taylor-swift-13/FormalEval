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

Example test_monotonic_2 : monotonic_spec [5; 4; 10; 10; 2; 1; 1; 1; 2; 3; 4; 1] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + (* Case: sorted_inc *)
      inversion Hinc as [| | ? ? ? Hle Htail]; subst.
      (* 5 <= 4 is false *)
      lia.
    + (* Case: sorted_dec *)
      inversion Hdec as [| | ? ? ? Hge Htail]; subst.
      (* 5 >= 4 is true, check next element *)
      inversion Htail as [| | ? ? ? Hge2 Htail2]; subst.
      (* 4 >= 10 is false *)
      lia.
Qed.