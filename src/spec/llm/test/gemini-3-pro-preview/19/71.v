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

(* Proof for the test case: input = ["two nine eight seven six five four one zero one zero"], output = "zero zero one one two four five six seven eight nine" *)
Example test_sort_numbers : sort_numbers_spec "two nine eight seven six five four one zero one zero" "zero zero one one two four five six seven eight nine".
Proof.
  unfold sort_numbers_spec.
  (* The input is not empty *)
  destruct (string_dec "two nine eight seven six five four one zero one zero" "") as [Heq | Hneq].
  - inversion Heq.
  - split.
    + (* Permutation proof *)
      vm_compute.
      (* Helper lemma to move an element from the middle of the list to the head *)
      assert (Hperm: forall A (x:A) l1 l2 l, Permutation l (l1 ++ l2) -> Permutation (x::l) (l1 ++ x :: l2)).
      { intros. apply Permutation_trans with (x :: l1 ++ l2). constructor. assumption. apply Permutation_middle. }
      
      (* Reorder elements to match the sorted list *)
      (* 1. two *)
      apply Hperm with (l1 := ["zero"; "zero"; "one"; "one"]). simpl.
      (* 2. nine *)
      apply Hperm with (l1 := ["zero"; "zero"; "one"; "one"; "four"; "five"; "six"; "seven"; "eight"]). simpl.
      (* 3. eight *)
      apply Hperm with (l1 := ["zero"; "zero"; "one"; "one"; "four"; "five"; "six"; "seven"]). simpl.
      (* 4. seven *)
      apply Hperm with (l1 := ["zero"; "zero"; "one"; "one"; "four"; "five"; "six"]). simpl.
      (* 5. six *)
      apply Hperm with (l1 := ["zero"; "zero"; "one"; "one"; "four"; "five"]). simpl.
      (* 6. five *)
      apply Hperm with (l1 := ["zero"; "zero"; "one"; "one"; "four"]). simpl.
      (* 7. four *)
      apply Hperm with (l1 := ["zero"; "zero"; "one"; "one"]). simpl.
      (* 8. one *)
      apply Hperm with (l1 := ["zero"; "zero"; "one"]). simpl.
      (* 9. zero *)
      apply Hperm with (l1 := []). simpl.
      (* 10. one *)
      apply Hperm with (l1 := ["zero"]). simpl.
      (* 11. zero *)
      apply Hperm with (l1 := []). simpl.
      
      apply Permutation_refl.
      
    + split.
      * (* Sorted proof *)
        vm_compute.
        repeat constructor.
      * (* Join proof *)
        reflexivity.
Qed.