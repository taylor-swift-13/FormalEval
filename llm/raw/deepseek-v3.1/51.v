
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Definition remove_vowels_spec (text : string) (result : string) : Prop :=
  result = filter (fun ch => negb (existsb (fun vowel => if Ascii.eqb ch vowel then true else false) 
                                          ("aeiouAEIOU"%string))) text.
