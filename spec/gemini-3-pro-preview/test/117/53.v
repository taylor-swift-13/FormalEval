Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* Specification Definitions *)

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a" | "e" | "i" | "o" | "u" 
  | "A" | "E" | "I" | "O" | "U" => true
  | _ => false
  end % char.

Fixpoint count_consonants (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if is_vowel c then 0 else 1) + count_consonants s'
  end.

Fixpoint split_words_aux (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => 
      if string_dec acc "" then [] else [acc]
  | String c s' =>
      if ascii_dec c " " then
        if string_dec acc "" then split_words_aux s' ""
        else acc :: split_words_aux s' ""
      else
        split_words_aux s' (acc ++ String c EmptyString)
  end.

Definition get_words (s : string) : list string :=
  split_words_aux s "".

Definition select_words_spec (s : string) (n : nat) (ans : list string) : Prop :=
  ans = filter (fun w => Nat.eqb (count_consonants w) n) (get_words s).

(* Test Case Proof *)

Example test_select_words : select_words_spec "apple banana cherapple banaapple banana chethe cat ine hatrrypypna cherryana chcerryry" 2 ["cat"].
Proof.
  unfold select_words_spec.
  unfold get_words.
  vm_compute.
  reflexivity.
Qed.