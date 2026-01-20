Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* Mapping from string representation to integer value *)
Definition to_int (s : string) : nat :=
  if string_dec s "zero" then 0
  else if string_dec s "one" then 1
  else if string_dec s "two" then 2
  else if string_dec s "three" then 3
  else if string_dec s "four" then 4
  else if string_dec s "five" then 5
  else if string_dec s "six" then 6
  else if string_dec s "seven" then 7
  else if string_dec s "eight" then 8
  else if string_dec s "nine" then 9
  else 0.

(* Comparison relation for strings based on their integer value *)
Definition str_le (s1 s2 : string) : Prop :=
  to_int s1 <= to_int s2.

(* Helper to check for space character *)
Definition is_space (c : ascii) : bool :=
  match c with
  | " "%char => true
  | _ => false
  end.

(* Helper function to split a string by spaces into a list of words *)
Fixpoint split_by_space (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => 
      if string_dec acc "" then [] else [acc]
  | String c s' =>
      if is_space c then
        if string_dec acc "" then split_by_space s' ""
        else acc :: split_by_space s' ""
      else split_by_space s' (acc ++ String c EmptyString)
  end.

Definition tokenize (s : string) : list string := split_by_space s "".

(* Helper function to join a list of words with spaces *)
Fixpoint join_with_space (l : list string) : string :=
  match l with
  | [] => ""
  | [s] => s
  | s :: xs => s ++ " " ++ join_with_space xs
  end.

(* Main specification for the sort_numbers function *)
Definition sort_numbers_spec (numbers : string) (result : string) : Prop :=
  if string_dec numbers "" then 
    result = ""
  else
    let input_tokens := tokenize numbers in
    let result_tokens := tokenize result in
    (* The result tokens must be a permutation of input tokens *)
    Permutation input_tokens result_tokens /\
    (* The result tokens must be sorted according to their numeric value *)
    Sorted str_le result_tokens /\
    (* The result string must be the joined representation of the sorted tokens *)
    result = join_with_space result_tokens.

Example test_sort_numbers : sort_numbers_spec "nine one zero five four one" "zero one one four five nine".
Proof.
  unfold sort_numbers_spec.
  destruct (string_dec "nine one zero five four one" "") as [Heq | Hneq].
  - discriminate.
  - split.
    + vm_compute.
      (* Target: ["zero"; "one"; "one"; "four"; "five"; "nine"] *)
      (* Current: ["nine"; "one"; "zero"; "five"; "four"; "one"] *)
      
      (* Move "zero" to front *)
      apply perm_trans with (l' := "nine" :: "zero" :: "one" :: "five" :: "four" :: "one" :: []).
      { apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := "zero" :: "nine" :: "one" :: "five" :: "four" :: "one" :: []).
      { apply perm_swap. }
      apply perm_skip.
      
      (* Move first "one" to front *)
      (* Current: ["nine"; "one"; "five"; "four"; "one"] *)
      apply perm_trans with (l' := "one" :: "nine" :: "five" :: "four" :: "one" :: []).
      { apply perm_swap. }
      apply perm_skip.
      
      (* Move second "one" to front *)
      (* Current: ["nine"; "five"; "four"; "one"] *)
      apply perm_trans with (l' := "nine" :: "five" :: "one" :: "four" :: []).
      { repeat apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := "nine" :: "one" :: "five" :: "four" :: []).
      { apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := "one" :: "nine" :: "five" :: "four" :: []).
      { apply perm_swap. }
      apply perm_skip.
      
      (* Move "four" to front *)
      (* Current: ["nine"; "five"; "four"] *)
      apply perm_trans with (l' := "nine" :: "four" :: "five" :: []).
      { apply perm_skip. apply perm_swap. }
      apply perm_trans with (l' := "four" :: "nine" :: "five" :: []).
      { apply perm_swap. }
      apply perm_skip.
      
      (* Swap "nine" and "five" *)
      (* Current: ["nine"; "five"] *)
      apply perm_swap.
      
    + split.
      * vm_compute. repeat constructor.
      * vm_compute. reflexivity.
Qed.