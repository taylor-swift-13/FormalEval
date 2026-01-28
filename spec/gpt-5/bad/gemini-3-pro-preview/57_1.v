Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition adj_le (l : list Z) : Prop :=
  forall i a b,
    nth_error l i = Some a ->
    nth_error l (S i) = Some b ->
    a <= b.

Definition adj_ge (l : list Z) : Prop :=
  forall i a b,
    nth_error l i = Some a ->
    nth_error l (S i) = Some b ->
    a >= b.

Definition monotonic_spec (l : list Z) (res : bool) : Prop :=
  res = true <-> adj_le l \/ adj_ge l.

Example test_monotonic : monotonic_spec [1; 2; 4; 10] true.
Proof.
  unfold monotonic_spec.
  split.
  - (* Left to Right *)
    intros _.
    left.
    unfold adj_le.
    intros i a b Ha Hb.
    (* Analyze index i to verify adj_le for each pair *)
    destruct i.
    + (* i = 0 *)
      simpl in Ha, Hb.
      injection Ha as <-.
      injection Hb as <-.
      lia.
    + destruct i.
      * (* i = 1 *)
        simpl in Ha, Hb.
        injection Ha as <-.
        injection Hb as <-.
        lia.
      * destruct i.
        -- (* i = 2 *)
           simpl in Ha, Hb.
           injection Ha as <-.
           injection Hb as <-.
           lia.
        -- (* i >= 3 *)
           destruct i.
           ++ (* i = 3 *)
              (* Ha is valid (index 3), Hb is invalid (index 4) *)
              simpl in Hb.
              discriminate Hb.
           ++ (* i >= 4 *)
              (* Ha is invalid (index >= 4) *)
              simpl in Ha.
              discriminate Ha.
  - (* Right to Left *)
    intros _.
    reflexivity.
Qed.