
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rtrigo1.
Require Import Coq.Reals.Rfunctions.
Import ListNotations.

Definition ceil (r : R) : Z :=
  if Rle_dec (IZR (up r)) r then up r else up r.

Fixpoint sum_squares_spec (lst : list R) (res : Z) : Prop :=
  res = fold_left (fun acc x => acc + (Z.pow 2 (ceil x))) lst 0.
