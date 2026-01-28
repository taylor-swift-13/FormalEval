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

Example test_digits_spec_large: digits_spec 3902482539585903843732859374089573948579380957409378540930757943758435987234095873947598347 349414592981611405398373936496217041015625.
Proof.
  unfold digits_spec.
  exists [7; 4; 3; 8; 9; 5; 7; 4; 9; 3; 7; 8; 5; 9; 0; 4; 3; 2; 7; 8; 9; 5; 3; 4; 8; 5; 7; 3; 4; 9; 7; 5; 7; 0; 3; 9; 0; 4; 5; 8; 7; 3; 9; 0; 4; 7; 5; 9; 0; 8; 3; 9; 7; 5; 8; 4; 9; 3; 7; 5; 9; 8; 0; 4; 7; 3; 9; 5; 8; 2; 3; 7; 3; 4; 8; 3; 0; 9; 5; 8; 5; 9; 3; 5; 2; 8; 4; 2; 0; 9; 3].
  split.
  - unfold decimal_digits.
    split.
    + lia.
    + split.
      * vm_compute. reflexivity.
      * unfold digits_range.
        repeat (constructor; [ unfold digit; lia | ]).
        apply Forall_nil.
  - vm_compute. reflexivity.
Qed.