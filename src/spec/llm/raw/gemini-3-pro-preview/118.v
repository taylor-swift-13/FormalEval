
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Definition is_vowel (c : ascii) : Prop :=
  In c ["a"%char; "e"%char; "i"%char; "o"%char; "u"%char; 
        "A"%char; "E"%char; "I"%char; "O"%char; "U"%char].

Definition satisfies_condition (s : string) (i : nat) : Prop :=
  exists c prev next,
    i > 0 /\
    String.get i s = Some c /\
    String.get (i - 1) s = Some prev /\
    String.get (i + 1) s = Some next /\
    is_vowel c /\
    ~ is_vowel prev /\
    ~ is_vowel next.

Definition get_closest_vowel_spec (word : string) (result : string) : Prop :=
  (exists i,
    satisfies_condition word i /\
    result = substring i 1 word /\
    (forall j, j > i -> ~ satisfies_condition word j))
  \/
  ((forall i, ~ satisfies_condition word i) /\ result = "").
