
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Definition pluck_spec (arr : list nat) (result : list nat) : Prop :=
  match arr with
  | nil => result = nil
  | _ =>
      (forall val, In val arr -> val mod 2 = 1) -> result = nil /\
      (exists min_even index,
          In min_even arr /\
          min_even mod 2 = 0 /\
          (forall val, In val arr -> val mod 2 = 0 -> min_even <= val) /\
          nth_error arr index = Some min_even /\
          result = [min_even; index] /\
          (forall i, nth_error arr i = Some min_even -> index <= i))
  end.
