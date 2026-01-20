
Require Import List String Ascii.
Require Import Arith.

Definition find_max_spec (words : list string) (result : string) : Prop :=
  exists max_word : string,
    In max_word words /\
    (forall word : string, In word words -> 
      let unique_chars_word := length (nodup string_dec (list_ascii_of_string word)) in
      let unique_chars_max := length (nodup string_dec (list_ascii_of_string max_word)) in
      unique_chars_word <= unique_chars_max /\
      (unique_chars_word = unique_chars_max -> max_word <= word)%string) /\
    result = max_word.
