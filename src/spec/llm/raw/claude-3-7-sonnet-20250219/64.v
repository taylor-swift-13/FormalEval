
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_vowel (c : ascii) : bool :=
  let l := "aeiouAEIOU" in
  existsb (Ascii.eqb c) (list_ascii_of_string l).

Definition is_y (c : ascii) : bool :=
  (Ascii.eqb c "y"%char) || (Ascii.eqb c "Y"%char).

Fixpoint count_vowels (l : list ascii) : nat :=
  match l with
  | [] => 0
  | c :: cs => (if is_vowel c then 1 else 0) + count_vowels cs
  end.

Definition vowels_count_spec (s : string) (count : nat) : Prop :=
  let chars := list_ascii_of_string s in
  match chars with
  | [] => count = 0
  | _ =>
    let base_count := count_vowels chars in
    if is_y (List.last chars "a"%char)
    then count = base_count + 1
    else count = base_count
  end.
