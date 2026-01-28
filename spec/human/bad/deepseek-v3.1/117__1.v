Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* Helper functions to determine character properties *)
Definition is_space (c : ascii) : bool :=
  Ascii.eqb c " "%char.

Definition is_letterb (c : ascii) : bool :=
  match c with
  | "A"%char | "B"%char | "C"%char | "D"%char | "E"%char | "F"%char | "G"%char | "H"%char |
    "I"%char | "J"%char | "K"%char | "L"%char | "M"%char | "N"%char | "O"%char | "P"%char |
    "Q"%char | "R"%char | "S"%char | "T"%char | "U"%char | "V"%char | "W"%char | "X"%char | "Y"%char | "Z"%char =>
      true
  | "a"%char | "b"%char | "c"%char | "d"%char | "e"%char | "f"%char | "g"%char | "h"%char |
    "i"%char | "j"%char | "k"%char | "l"%char | "m"%char | "n"%char | "o"%char | "p"%char |
    "q"%char | "r"%char | "s"%char | "t"%char | "u"%char | "v"%char | "w"%char | "x"%char | "y"%char | "z"%char =>
      true
  | _ => false
  end.

Definition is_vowelb (c : ascii) : bool :=
  Ascii.eqb c "a"%char || Ascii.eqb c "e"%char || Ascii.eqb c "i"%char ||
  Ascii.eqb c "o"%char || Ascii.eqb c "u"%char ||
  Ascii.eqb c "A"%char || Ascii.eqb c "E"%char || Ascii.eqb c "I"%char ||
  Ascii.eqb c "O"%char || Ascii.eqb c "U"%char.

(* Function to split string into words based on spaces *)
Fixpoint split_words (l : list ascii) : list (list ascii) :=
  match l with
  | [] => []
  | _ =>
    let fix take_word (l' : list ascii) (acc : list ascii) : (list ascii) * list ascii :=
        match l' with
        | [] => (rev acc, [])
        | c :: csa =>
          if is_space c then (rev acc, csa)
          else take_word csa (c :: acc)
        end
    in
    let (w, rest) := take_word l [] in
    if w =? [] then split_words rest else w :: split_words rest
  end.

(* Count number of consonants in a word *)
Definition count_consonants (w : list ascii) : nat :=
  fold_left (fun acc c =>
    if andb (is_letterb c) (negb (is_vowelb c)) then S acc else acc) w 0.

(* Check if a word has exactly n consonants *)
Definition word_has_n_consonants (w : list ascii) (n : nat) : bool :=
  Nat.eqb (count_consonants w) n.

(* Convert input string to list of words *)
Definition words_of_string (s : string) : list (list ascii) :=
  split_words (list_ascii_of_string s).

(* Filter words based on consonant count *)
Definition select_words (ws : list (list ascii)) (n : nat) : list (list ascii) :=
  filter (fun w => word_has_n_consonants w n) ws.

(* Main function: extract words with specific consonant count as strings *)
Definition select_words_from_string (s : string) (n : nat) : list string :=
  let ws := words_of_string s in
  let selected := select_words ws n in
  map string_of_list_ascii selected.

(* Proof of the example: select the word "little" when n=4 *)
Example test_select_words_4_mary_had_a_little_lamb :
  select_words_from_string "Mary had a little lamb" 4 = ["little"].
Proof.
  unfold select_words_from_string, select_words, words_of_string, word_has_n_consonants, count_consonants.
  simpl.

  (* Let's evaluate the split_words step explicitly *)
  (* Input list ascii of the string "Mary had a little lamb" *)
  remember (list_ascii_of_string "Mary had a little lamb") as lst.

  (* Work out split_words on this list *)
  assert (Hsplit :
    split_words lst =
      [list_ascii_of_string "Mary"; list_ascii_of_string "had"; list_ascii_of_string "a"; list_ascii_of_string "little"; list_ascii_of_string "lamb"]).
  {
    subst lst.
    (* The split is straightforward: based on space characters *)
    (* The function `split_words` correctly splits at spaces; given the original string, this holds *)
    reflexivity.
  }
  rewrite Hsplit.

  (* For each word, compute the number of consonants *)
  (* "Mary" : M (consonant), a (vowel), r (consonant), y (consonant) -> 3 *)
  (* "had" : h (consonant), a (vowel), d (consonant) -> 2 *)
  (* "a" : vowel only -> 0 *)
  (* "little" : l (consonant), i (vowel), t (consonant), t (consonant), l (consonant), e (vowel) -> 4 *)
  (* "lamb" : l (consonant), a (vowel), m (consonant), b (consonant) -> 3 *)

  (* The filter picks only "little" because it has exactly 4 consonants *)
  simpl; reflexivity.
Qed.