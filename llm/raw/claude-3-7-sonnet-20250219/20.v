
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.

Import ListNotations.

Definition find_closest_elements_spec (numbers : list R) (p : R * R) : Prop :=
  length numbers >= 2 /\
  (* p is a pair taken from numbers *)
  In (fst p) numbers /\
  In (snd p) numbers /\
  fst p <= snd p /\
  (* for every adjacent pair in the sorted list, the difference is at least that of p *)
  let sorted := sort Rle_dec numbers in
  (* p is an adjacent pair in sorted *)
  (exists i, i < length sorted - 1 /\
             nth i sorted 0 = fst p /\
             nth (i + 1) sorted 0 = snd p) /\
  (* minimal difference *)
  forall a b,
    In a numbers ->
    In b numbers ->
    a <= b ->
    (exists j, j < length sorted - 1 /\
               nth j sorted 0 = a /\
               nth (j + 1) sorted 0 = b) ->
    (snd p - fst p) <= (b - a).
