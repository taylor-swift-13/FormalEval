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

Example test_digits_spec_large: digits_spec 1234567891011121314151617181920212223242526272829303132333435363738394041424344454647484950515251 27813241521305666015625.
Proof.
  unfold digits_spec.
  exists [1; 5; 2; 5; 1; 5; 0; 5; 9; 4; 8; 4; 7; 4; 6; 4; 5; 4; 4; 4; 3; 4; 2; 4; 1; 4; 0; 4; 9; 3; 8; 3; 7; 3; 6; 3; 5; 3; 4; 3; 3; 3; 2; 3; 1; 3; 0; 3; 9; 2; 8; 2; 7; 2; 6; 2; 5; 2; 4; 2; 3; 2; 2; 2; 1; 2; 0; 2; 9; 1; 8; 1; 7; 1; 6; 1; 5; 1; 4; 1; 3; 1; 2; 1; 1; 1; 0; 1; 9; 8; 7; 6; 5; 4; 3; 2; 1].
  split.
  - unfold decimal_digits.
    split.
    + vm_compute. reflexivity.
    + split.
      * vm_compute. reflexivity.
      * unfold digits_range.
        repeat (apply Forall_cons; [ unfold digit; lia | ]).
        apply Forall_nil.
  - vm_compute. reflexivity.
Qed.