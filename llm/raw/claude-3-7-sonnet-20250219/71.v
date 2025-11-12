
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.QArith.Qround.

Open Scope R_scope.

Definition valid_triangle (a b c : R) : Prop :=
  a + b > c /\ a + c > b /\ b + c > a /\ a > 0 /\ b > 0 /\ c > 0.

Definition heron_area (a b c : R) : R :=
  let p := (a + b + c) / 2 in
  sqrt (p * (p - a) * (p - b) * (p - c)).

Definition round2 (r : R) : R :=
  INR (Z.to_nat (up (r * 100))) / 100.

Definition triangle_area_spec (a b c : R) (res : R) : Prop :=
  (valid_triangle a b c /\ res = round2 (heron_area a b c)) \/ ((~ valid_triangle a b c) /\ res = (-1)).

