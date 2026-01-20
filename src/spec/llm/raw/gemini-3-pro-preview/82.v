
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition prime_length_spec (s : string) (res : bool) : Prop :=
  res = true <-> Nat.Prime (String.length s).
