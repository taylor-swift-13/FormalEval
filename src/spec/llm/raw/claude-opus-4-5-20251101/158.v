
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition char := Ascii.ascii.

Fixpoint char_in_list (c : char) (l : list char) : bool :=
  match l with
  | [] => false
  | h :: t => if Ascii.eqb c h then true else char_in_list c t
  end.

Fixpoint unique_chars (s : list char) (seen : list char) : list char :=
  match s with
  | [] => seen
  | h :: t => if char_in_list h seen 
              then unique_chars t seen 
              else unique_chars t (h :: seen)
  end.

Definition count_unique_chars (s : string) : nat :=
  length (unique_chars (list_ascii_of_string s) []).

Definition string_lt (s1 s2 : string) : bool :=
  match String.compare s1 s2 with
  | Lt => true
  | _ => false
  end.

Definition is_better_word (word ans : string) (word_cnt ans_cnt : nat) : bool :=
  (word_cnt >? ans_cnt) || ((word_cnt =? ans_cnt) && string_lt word ans).

Fixpoint find_max_helper (words : list string) (mx_ch_cnt : nat) (ans : string) : string :=
  match words with
  | [] => ans
  | word :: rest =>
      let ch_cnt := count_unique_chars word in
      if is_better_word word ans ch_cnt mx_ch_cnt
      then find_max_helper rest ch_cnt word
      else find_max_helper rest mx_ch_cnt ans
  end.

Definition find_max (words : list string) : string :=
  find_max_helper words 0 "".

Definition has_max_unique_chars (word : string) (words : list string) : Prop :=
  forall w, In w words -> count_unique_chars w <= count_unique_chars word.

Definition is_lexicographically_first_among_max (word : string) (words : list string) : Prop :=
  forall w, In w words -> 
    count_unique_chars w = count_unique_chars word -> 
    String.compare word w <> Gt.

Definition find_max_spec (words : list string) (result : string) : Prop :=
  match words with
  | [] => result = ""
  | _ => In result words /\
         has_max_unique_chars result words /\
         is_lexicographically_first_among_max result words
  end.
