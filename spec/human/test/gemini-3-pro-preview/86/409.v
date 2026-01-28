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

(* Example Proof for Test Case *)

Definition test_input := 
  "PpassswPyIn computer sciequicknpasss " ++ 
  String (ascii_of_nat 9) (String (ascii_of_nat 10) (String (ascii_of_nat 32) (String (ascii_of_nat 12) 
  "A B C   D E F     G H I      yintegrammingce, sciequoficknce,garbage collectin is a form oThef automatic memory manageabcIn coomputer science, garbage coquickmanagemendOTSAbCdEfGuhIjKlMnOMpQrStIHGFEDCBAment.thonordMyyton"))).

Definition test_output := 
  "IPPanpssswy cemoprtu acceiiknpqssssu " ++ 
  String (ascii_of_nat 9) (String (ascii_of_nat 10) (String (ascii_of_nat 32) (String (ascii_of_nat 12) 
  "A B C   D E F     G H I      ,aceeggiimmnnrty ,aabccceeefggiiknoqrsu cceillnot is a fmor Tefho aacimottu emmory Iaaabcegmnn cemooprtu ,cceeins aabeggr .AABCCDEEFGGHIIKMMMOOQSSTaabccdddeeefghhijklmmmnnnnnnoooopqrrttttuuyy"))).

Example problem_86_test : problem_86_spec test_input test_output.
Proof.
  unfold problem_86_spec.
  unfold anti_shuffle_impl.
  unfold test_input.
  unfold test_output.
  vm_compute.
  reflexivity.
Qed.