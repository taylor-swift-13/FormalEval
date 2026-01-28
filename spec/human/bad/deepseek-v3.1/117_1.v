Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* Assuming the functions are already defined as above:
   is_vowel, count_consonants, split_words, select_words_impl, select_words *)

(* Here, for completeness, we re-define select_words as the user provided functions suggest. *)
Definition select_words (s : string) (n : nat) : list string :=
  let l := list_ascii_of_string s in
  let res := select_words_impl l n in
  map string_of_list_ascii res.

(* Example test case *)
Example select_words_example :
  select_words "Mary had a little lamb" 4 = ["little"].
Proof.
  unfold select_words.
  simpl.

  (* Since the correctness depends on the correctness of select_words_impl,
     and the provided code is assumed to be correct and available,
     the key is to argue about the implementation given the string. *)

  (* "Mary had a little lamb" split into words: ["Mary"; "had"; "a"; "little"; "lamb"] *)
  (* For each of these words, count_consonants and filter *)

  (* "Mary": M r y -> consonants: M, r, y (y not a vowel) -> 3 *)
  (* "had": h a d -> consonants: h, d -> 2 *)
  (* "a": a -> 0 *)
  (* "little": l i t t l e -> consonants: l, t, t, l -> 4 *)
  (* "lamb": l a m b -> consonants: l, m, b -> 3 *)

  (* So only "little" qualifies for n=4 *)

  (* The filter should produce only ["little"] *)

  reflexivity.
Qed.