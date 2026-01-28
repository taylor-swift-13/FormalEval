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

Example test_monotonic_2 : monotonic_spec [1; 3; 4; 5; 4; 0; 3; 2] false.
Proof.
  unfold monotonic_spec.
  split.
  - intros H. discriminate.
  - intros [Hinc | Hdec].
    + (* sorted_inc case *)
      inversion Hinc as [| x1 | x1 y1 l1 Hle1 Htail1]; subst.
      inversion Htail1 as [| x2 | x2 y2 l2 Hle2 Htail2]; subst.
      inversion Htail2 as [| x3 | x3 y3 l3 Hle3 Htail3]; subst.
      inversion Htail3 as [| x4 | x4 y4 l4 Hle4 Htail4]; subst.
      lia.
    + (* sorted_dec case *)
      inversion Hdec as [| x1 | x1 y1 l1 Hge1 Htail1]; subst.
      lia.
Qed.