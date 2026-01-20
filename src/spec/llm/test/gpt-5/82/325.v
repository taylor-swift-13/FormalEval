Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Fixpoint has_divisor_upto (n k : nat) : bool :=
  match k with
  | 0 => false
  | 1 => false
  | S k' => orb (Nat.eqb (Nat.modulo n (S k')) 0) (has_divisor_upto n k')
  end.

Definition is_primeb (a : nat) : bool :=
  negb (orb (Nat.ltb a 2) (has_divisor_upto a (Nat.pred a))).

Definition prime_length_spec (s : string) (b : bool) : Prop :=
  b = is_primeb (String.length s).

Example prime_length_spec_The_quick_brown_fox_jumps_Wxjmnzover_the_lazxylophfoxonisct_dog_WxjmonzoveThis_false :
  prime_length_spec "The quick brown fox jumps Wxjmnzover the lazxylophfoxonisct dog.WxjmonzoveThis"%string false.
Proof.
  unfold prime_length_spec.
  vm_compute.
  reflexivity.
Qed.