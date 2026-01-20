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

Example test_case : digits_spec 5 5.
Proof.
  unfold digits_spec.
  (* We propose the list [5] as the decimal representation of 5 *)
  exists [5].
  split.
  - (* Prove decimal_digits 5 [5] *)
    unfold decimal_digits.
    split.
    + (* 0 < 5 *)
      lia.
    + split.
      * (* val10 [5] = 5 *)
        simpl. lia.
      * (* digits_range [5] *)
        unfold digits_range.
        constructor.
        -- (* digit 5 *)
           unfold digit. lia.
        -- (* Forall nil *)
           constructor.
  - (* Prove result calculation *)
    simpl.
    (* Z.odd 5 is true, so we calculate 5 * 1 *)
    reflexivity.
Qed.