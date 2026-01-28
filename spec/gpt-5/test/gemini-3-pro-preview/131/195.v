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

Example test_digits_spec_large: digits_spec 182937457814614279640075438629345987263878749129823578184719333882439 21369469725649569313125.
Proof.
  unfold digits_spec.
  exists [9; 3; 4; 2; 8; 8; 3; 3; 3; 9; 1; 7; 4; 8; 1; 8; 7; 5; 3; 2; 8; 9; 2; 1; 9; 4; 7; 8; 7; 8; 3; 6; 2; 7; 8; 9; 5; 4; 3; 9; 2; 6; 8; 3; 4; 5; 7; 0; 0; 4; 6; 9; 7; 2; 4; 1; 6; 4; 1; 8; 7; 5; 4; 7; 3; 9; 2; 8; 1].
  split.
  - unfold decimal_digits.
    split.
    + vm_compute. reflexivity.
    + split.
      * vm_compute. reflexivity.
      * unfold digits_range.
        repeat (constructor; try (unfold digit; lia)).
  - vm_compute. reflexivity.
Qed.