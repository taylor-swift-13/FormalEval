
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Definition uppercase_vowelb (a : ascii) : bool :=
  orb (Nat.eqb (nat_of_ascii a) (nat_of_ascii "A"%char))
      (orb (Nat.eqb (nat_of_ascii a) (nat_of_ascii "E"%char))
           (orb (Nat.eqb (nat_of_ascii a) (nat_of_ascii "I"%char))
                (orb (Nat.eqb (nat_of_ascii a) (nat_of_ascii "O"%char))
                     (Nat.eqb (nat_of_ascii a) (nat_of_ascii "U"%char))))).

Fixpoint count_upper_rec (l : list ascii) (i : nat) : nat :=
  match l with
  | [] => 0
  | a :: tl =>
      let add :=
        if Nat.even i
        then if uppercase_vowelb a then 1 else 0
        else 0 in
      Nat.add add (count_upper_rec tl (S i))
  end.

Definition count_upper_spec (s : string) (cnt : nat) : Prop :=
  cnt = count_upper_rec (list_of_string s) 0.
