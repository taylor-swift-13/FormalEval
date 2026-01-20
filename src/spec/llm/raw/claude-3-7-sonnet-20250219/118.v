
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

Definition is_vowel (ch : ascii) : bool :=
  let vowels := "aeiouAEIOU"%string in
  existsb (Ascii.eqb ch) (list_ascii_of_string vowels).

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Definition get_closest_vowel_spec (word : string) (res : string) : Prop :=
  let n := String.length word in
  (res = "" /\ 
    (forall i : nat,
      1 <= i < n - 1 ->
      let c := (nth_default " " word i) in
      negb (is_vowel c) \/ 
      (* the vowel is not between two consonants *)
      is_vowel (nth_default " " word (i-1)) = true \/
      is_vowel (nth_default " " word (i+1)) = true))
  \/
  (exists i : nat,
    1 <= i < n - 1 /\
    nth_default " " word i = hd " " (string_to_list res) /\
    is_vowel (nth_default " " word i) = true /\
    is_vowel (nth_default " " word (i-1)) = false /\
    is_vowel (nth_default " " word (i+1)) = false /\
    (forall j : nat,
      i < j < n - 1 ->
      negb (is_vowel (nth_default " " word j) = true /\
            is_vowel (nth_default " " word (j-1)) = false /\
            is_vowel (nth_default " " word (j+1)) = false))).

(* Auxiliary definitions *)
Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Definition nth_default (d : ascii) (s : string) (n : nat) : ascii :=
  nth n (string_to_list s) d.
