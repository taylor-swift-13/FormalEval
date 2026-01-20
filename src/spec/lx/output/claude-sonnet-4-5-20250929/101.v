Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_delimiter (c : ascii) : bool :=
  match c with
  | ","%char | " "%char => true
  | _ => false
  end.

Fixpoint words_string_aux (current_word : list ascii) (input : list ascii) : list (list ascii) :=
  match input with
  | [] =>
    match current_word with
    | [] => []
    | _ => [current_word]
    end
  | c :: cs =>
    if is_delimiter c then
      match current_word with
      | [] => words_string_aux [] cs
      | _ => current_word :: words_string_aux [] cs
      end
    else
      words_string_aux (current_word ++ [c]) cs
  end.

Definition words_string_list (s : list ascii) : list (list ascii) :=
  words_string_aux [] s.

Definition non_delimiter_char (c : ascii) : Prop :=
  is_delimiter c = false.

Definition words_string_list_spec (s : list ascii) (result : list (list ascii)) : Prop :=
  result = words_string_list s /\
  Forall (fun word => Forall non_delimiter_char word) result.

Lemma non_delimiter_H : non_delimiter_char "H"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Lemma non_delimiter_i : non_delimiter_char "i"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Lemma non_delimiter_m : non_delimiter_char "m"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Lemma non_delimiter_y : non_delimiter_char "y"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Lemma non_delimiter_n : non_delimiter_char "n"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Lemma non_delimiter_a : non_delimiter_char "a"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Lemma non_delimiter_e : non_delimiter_char "e"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Lemma non_delimiter_s : non_delimiter_char "s"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Lemma non_delimiter_J : non_delimiter_char "J"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Lemma non_delimiter_o : non_delimiter_char "o"%char.
Proof.
  unfold non_delimiter_char, is_delimiter.
  reflexivity.
Qed.

Example test_words_string :
  words_string_list_spec 
    ["H"%char; "i"%char; ","%char; " "%char; "m"%char; "y"%char; " "%char; 
     "n"%char; "a"%char; "m"%char; "e"%char; " "%char; "i"%char; "s"%char; " "%char; 
     "J"%char; "o"%char; "h"%char; "n"%char]
    [["H"%char; "i"%char]; ["m"%char; "y"%char]; ["n"%char; "a"%char; "m"%char; "e"%char]; 
     ["i"%char; "s"%char]; ["J"%char; "o"%char; "h"%char; "n"%char]].
Proof.
  unfold words_string_list_spec.
  split.
  - unfold words_string_list.
    simpl.
    reflexivity.
  - repeat constructor; 
    try apply non_delimiter_H;
    try apply non_delimiter_i;
    try apply non_delimiter_m;
    try apply non_delimiter_y;
    try apply non_delimiter_n;
    try apply non_delimiter_a;
    try apply non_delimiter_e;
    try apply non_delimiter_s;
    try apply non_delimiter_J;
    try apply non_delimiter_o;
    unfold non_delimiter_char, is_delimiter; reflexivity.
Qed.