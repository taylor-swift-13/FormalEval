
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition is_vowel (ch : ascii) : bool :=
  let c := nat_of_ascii ch in
  match c with
  | 97 | 101 | 105 | 111 | 117 => true (* a, e, i, o, u *)
  | 65 | 69 | 73 | 79 | 85 => true     (* A, E, I, O, U *)
  | _ => false
  end.

Definition is_consonant (ch : ascii) : bool :=
  negb (is_vowel ch).

Fixpoint count_consonants (word : list ascii) : nat :=
  match word with
  | [] => 0
  | ch :: rest => (if is_consonant ch then 1 else 0) + count_consonants rest
  end.

Fixpoint split_by_space (s : list ascii) : list (list ascii) :=
  match s with
  | [] => [[]]
  | ch :: rest =>
    if Nat.eqb (nat_of_ascii ch) 32 then
      [] :: split_by_space rest
    else
      match split_by_space rest with
      | [] => [[ch]]
      | w :: ws => (ch :: w) :: ws
      end
  end.

Definition is_non_empty (word : list ascii) : bool :=
  match word with
  | [] => false
  | _ => true
  end.

Definition select_words_spec (s : list ascii) (n : nat) (result : list (list ascii)) : Prop :=
  let words := split_by_space s in
  let non_empty_words := filter is_non_empty words in
  result = filter (fun word => Nat.eqb (count_consonants word) n) non_empty_words.
