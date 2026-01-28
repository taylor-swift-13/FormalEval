Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

(* Provided Definitions *)

Definition is_space_bool (c : ascii) : bool :=
  if ascii_dec c " "%char then true else false.

Fixpoint insert_char (c : ascii) (s : string) : string :=
  match s with
  | EmptyString => String c EmptyString
  | String h t =>
      if Nat.leb (nat_of_ascii c) (nat_of_ascii h) then
        String c s
      else
        String h (insert_char c t)
  end.

Fixpoint sort_chars (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String h t => insert_char h (sort_chars t)
  end.

Fixpoint anti_shuffle_aux (s : string) (acc : string) : string :=
  match s with
  | EmptyString => sort_chars acc
  | String c rest =>
      if is_space_bool c then
        (sort_chars acc) ++ (String c EmptyString) ++ (anti_shuffle_aux rest EmptyString)
      else
        anti_shuffle_aux rest (String c acc)
  end.

Definition anti_shuffle_impl (s : string) : string :=
  anti_shuffle_aux s EmptyString.

Definition problem_86_pre (s : string) : Prop := True.

Definition problem_86_spec (s s_out : string) : Prop :=
  s_out = anti_shuffle_impl s.

Definition codes_to_string (l : list nat) : string :=
  List.fold_right (fun n s => String (ascii_of_nat n) s) EmptyString l.

Definition test_input_codes : list nat :=
  [112; 121; 113; 117; 105] ++ [32] ++
  [9; 10] ++ [32] ++
  [9; 10; 12; 11; 65] ++ [32] ++
  [66] ++ [32] ++ [67] ++ [32; 32; 32] ++ [68] ++ [32] ++ [69] ++ [32] ++ [70] ++ [32; 32; 32; 32; 32; 32] ++
  [73] ++ [32; 32; 32; 32; 32; 32] ++
  [12; 11; 65] ++ [32] ++
  [66] ++ [32] ++ [67] ++ [32; 32; 32] ++ [68] ++ [32] ++ [69] ++ [32] ++ [70] ++ [32; 32; 32; 32; 32] ++
  [71] ++ [32] ++ [72] ++ [32] ++ [73] ++ [32; 32; 32; 32; 32; 32] ++
  [107; 116; 104; 111; 121; 110; 109].

Definition test_output_codes : list nat :=
  [105; 112; 113; 117; 121] ++ [32] ++
  [9; 10] ++ [32] ++
  [9; 10; 11; 12; 65] ++ [32] ++
  [66] ++ [32] ++ [67] ++ [32; 32; 32] ++ [68] ++ [32] ++ [69] ++ [32] ++ [70] ++ [32; 32; 32; 32; 32; 32] ++
  [73] ++ [32; 32; 32; 32; 32; 32] ++
  [11; 12; 65] ++ [32] ++
  [66] ++ [32] ++ [67] ++ [32; 32; 32] ++ [68] ++ [32] ++ [69] ++ [32] ++ [70] ++ [32; 32; 32; 32; 32] ++
  [71] ++ [32] ++ [72] ++ [32] ++ [73] ++ [32; 32; 32; 32; 32; 32] ++
  [104; 107; 109; 110; 111; 116; 121].

Example problem_86_test : problem_86_spec (codes_to_string test_input_codes) (codes_to_string test_output_codes).
Proof.
  unfold problem_86_spec.
  unfold anti_shuffle_impl.
  vm_compute.
  reflexivity.
Qed.