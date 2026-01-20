
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition is_upper_vowel (c : ascii) : bool :=
  match c with
  | "A" | "E" | "I" | "O" | "U" => true
  | _ => false
  end%char.

Definition count_upper_spec (s : string) (cnt : nat) : Prop :=
  cnt = List.length (filter (fun i => Nat.even i && is_upper_vowel (String.get i s)) (seq 0 (String.length s))).
