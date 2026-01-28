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

Example test_digits_spec_62: digits_spec 62 0.
Proof.
  (* Unfold the main specification *)
  unfold digits_spec.
  
  (* Provide the witness list [2; 6] (little-endian representation of 62) *)
  exists [2; 6].
  
  (* Split into the validity of the digits and the result calculation *)
  split.
  - (* Prove decimal_digits 62 [2; 6] *)
    unfold decimal_digits.
    split.
    + (* 0 < 62 *)
      lia.
    + split.
      * (* val10 [2; 6] = 62 *)
        simpl. lia.
      * (* digits_range [2; 6] *)
        unfold digits_range.
        constructor.
        -- (* digit 2 *)
           unfold digit. lia.
        -- constructor.
           ++ (* digit 6 *)
              unfold digit. lia.
           ++ (* Forall digit [] *)
              constructor.
  - (* Prove 0 = (if has_oddb [2; 6] then prod_odd [2; 6] else 0) *)
    simpl.
    (* Z.odd 2 and Z.odd 6 are false, so has_oddb returns false *)
    reflexivity.
Qed.