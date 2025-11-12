
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.
Require Import Coq.micromega.Lia.

Definition ceil (x : R) : Z :=
  match total_order_T x (IZR (up x)) with
  | inleft _ => up x
  | inright _ => up x
  end.

Fixpoint sum_squares_spec (lst : list R) (result : Z) : Prop :=
  let squared_ceil := map (fun x => (ceil x) ^ 2) lst in
  result = fold_right Z.add 0%Z squared_ceil.
