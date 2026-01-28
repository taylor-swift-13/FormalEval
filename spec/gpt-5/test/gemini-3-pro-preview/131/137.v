Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.
Import ListNotations.

Fixpoint val10 (ds : list Z) : Z :=
  match ds with
  | [] => 0
  | d :: tl => d + 10 * val10 tl
  end.

Definition digit (d : Z) : Prop := 0 <= d < 10.

Definition digits_range (ds : list Z) : Prop := Forall digit ds.

Fixpoint prod_odd (ds : list Z) : Z :=
  match ds with
  | [] => 1
  | d :: tl => (if Z.odd d then d else 1) * prod_odd tl
  end.

Fixpoint has_oddb (ds : list Z) : bool :=
  match ds with
  | [] => false
  | d :: tl => orb (Z.odd d) (has_oddb tl)
  end.

Definition decimal_digits (n : Z) (ds : list Z) : Prop :=
  0 < n /\ val10 ds = n /\ digits_range ds.

Definition digits_spec (n : Z) (res : Z) : Prop :=
  exists ds, decimal_digits n ds /\ res = (if has_oddb ds then prod_odd ds else 0).

Example test_digits_spec_large: digits_spec 124834738571930288374895092375830274843252127479238048384758941827309258429539458173975894729347586 47338934509524145086063972158203125.
Proof.
  unfold digits_spec.
  exists [6; 8; 5; 7; 4; 3; 9; 2; 7; 4; 9; 8; 5; 7; 9; 3; 7; 1; 8; 5; 4; 9; 3; 5; 9; 2; 4; 8; 5; 2; 9; 0; 3; 7; 2; 8; 1; 4; 9; 8; 5; 7; 4; 8; 3; 8; 4; 0; 8; 3; 2; 9; 7; 4; 7; 2; 1; 2; 5; 2; 3; 4; 8; 4; 7; 2; 0; 3; 8; 5; 7; 3; 2; 9; 0; 5; 9; 8; 4; 7; 3; 8; 8; 2; 0; 3; 9; 1; 7; 5; 8; 3; 7; 4; 3; 8; 4; 2; 1].
  split.
  - unfold decimal_digits. split.
    + vm_compute. reflexivity.
    + split.
      * vm_compute. reflexivity.
      * unfold digits_range. repeat (constructor; [unfold digit; lia | ]). constructor.
  - vm_compute. reflexivity.
Qed.