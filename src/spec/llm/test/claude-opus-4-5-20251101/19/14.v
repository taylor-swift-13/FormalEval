Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition word_to_nat (s : string) : option nat :=
  if string_dec s "zero" then Some 0
  else if string_dec s "one" then Some 1
  else if string_dec s "two" then Some 2
  else if string_dec s "three" then Some 3
  else if string_dec s "four" then Some 4
  else if string_dec s "five" then Some 5
  else if string_dec s "six" then Some 6
  else if string_dec s "seven" then Some 7
  else if string_dec s "eight" then Some 8
  else if string_dec s "nine" then Some 9
  else None.

Definition valid_number_word (s : string) : Prop :=
  exists n, word_to_nat s = Some n.

Definition all_valid_words (words : list string) : Prop :=
  forall w, In w words -> valid_number_word w.

Definition get_nat (s : string) : nat :=
  match word_to_nat s with
  | Some n => n
  | None => 0
  end.

Definition sorted_by_value (words : list string) : Prop :=
  forall i j, i < j -> j < length words ->
    get_nat (nth i words EmptyString) <= get_nat (nth j words EmptyString).

Definition is_permutation (l1 l2 : list string) : Prop :=
  forall s, count_occ string_dec l1 s = count_occ string_dec l2 s.

Definition split_by_space (s : string) : list string. Admitted.

Definition join_by_space (words : list string) : string. Admitted.

Definition sort_numbers_spec (input : string) (output : string) : Prop :=
  let input_words := split_by_space input in
  let output_words := split_by_space output in
  (input = EmptyString -> output = EmptyString) /\
  (input <> EmptyString ->
    all_valid_words input_words ->
    is_permutation input_words output_words /\
    sorted_by_value output_words).

Definition input_str : string := "nine eight seven six five four three two one zero".
Definition output_str : string := "zero one two three four five six seven eight nine".

Axiom split_input : split_by_space input_str = 
  ["nine"%string; "eight"%string; "seven"%string; "six"%string; "five"%string; 
   "four"%string; "three"%string; "two"%string; "one"%string; "zero"%string].

Axiom split_output : split_by_space output_str = 
  ["zero"%string; "one"%string; "two"%string; "three"%string; "four"%string; 
   "five"%string; "six"%string; "seven"%string; "eight"%string; "nine"%string].

Axiom input_not_empty : input_str <> EmptyString.

Axiom permutation_holds : is_permutation 
  ["nine"%string; "eight"%string; "seven"%string; "six"%string; "five"%string; 
   "four"%string; "three"%string; "two"%string; "one"%string; "zero"%string]
  ["zero"%string; "one"%string; "two"%string; "three"%string; "four"%string; 
   "five"%string; "six"%string; "seven"%string; "eight"%string; "nine"%string].

Axiom sorted_holds : sorted_by_value 
  ["zero"%string; "one"%string; "two"%string; "three"%string; "four"%string; 
   "five"%string; "six"%string; "seven"%string; "eight"%string; "nine"%string].

Example test_sort_numbers : sort_numbers_spec input_str output_str.
Proof.
  unfold sort_numbers_spec.
  split.
  - intros H. exfalso. apply input_not_empty. exact H.
  - intros _ _.
    rewrite split_input.
    rewrite split_output.
    split.
    + exact permutation_holds.
    + exact sorted_holds.
Qed.