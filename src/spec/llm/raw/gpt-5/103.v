Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Open Scope Z_scope.
Open Scope string_scope.

Fixpoint string_of_bits_high (bits : list bool) : string :=
  match bits with
  | nil => EmptyString
  | b :: t => String (if b then "1"%char else "0"%char) (string_of_bits_high t)
  end.

Fixpoint value_of_bits_high (bits : list bool) : Z :=
  match bits with
  | nil => 0
  | b :: t => (if b then 1 else 0) * Z.pow 2 (Z.of_nat (List.length t)) + value_of_bits_high t
  end.

Definition BitsOf (z : Z) (bits : list bool) : Prop :=
  value_of_bits_high bits = z
  ∧ ((z = 0 ∧ bits = false :: nil) ∨ (0 < z ∧ exists t, bits = true :: t)).

Definition BinStringOfPython (z : Z) (s : string) : Prop :=
  (0 <= z ∧ exists bits, s = String.append "0b" (string_of_bits_high bits) ∧ BitsOf z bits)
  ∨ (z < 0 ∧ exists bits, s = String.append "-0b" (string_of_bits_high bits) ∧ BitsOf (-z) bits).

Definition round_half_to_even (s : Z) : Z :=
  let q := Z.div s 2 in
  if Z.eqb (Z.mod s 2) 0 then q else if Z.even q then q else q + 1.

Definition rounded_avg_spec (n m : Z) (out : sum Z string) : Prop :=
  (n > m ∧ out = inl (-1)) ∨
  (n <= m ∧ exists s, out = inr s ∧ BinStringOfPython (round_half_to_even (n + m)) s).