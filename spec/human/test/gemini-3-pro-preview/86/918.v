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

Fixpoint string_of_nats (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: rest => String (ascii_of_nat n) (string_of_nats rest)
  end.

(* 
   Input: " 	\n\f\vA B C   D E F     G H  I      G"
   ASCII values:
   Space=32, Tab=9, NL=10, FF=12, VT=11, A=65, B=66, C=67, D=68, E=69, F=70, G=71, H=72, I=73
*)
Definition input_nats : list nat := 
  [32; 9; 10; 12; 11; 65; 32; 66; 32; 67; 32; 32; 32; 68; 32; 69; 32; 70; 32; 32; 32; 32; 32; 71; 32; 72; 32; 32; 73; 32; 32; 32; 32; 32; 32; 71].

(* 
   Output: " 	\n\v\fA B C   D E F     G H  I      G"
   The first word "	\n\f\vA" (9, 10, 12, 11, 65) is sorted to "	\n\v\fA" (9, 10, 11, 12, 65).
   Other words are single letters and remain unchanged.
*)
Definition output_nats : list nat := 
  [32; 9; 10; 11; 12; 65; 32; 66; 32; 67; 32; 32; 32; 68; 32; 69; 32; 70; 32; 32; 32; 32; 32; 71; 32; 72; 32; 32; 73; 32; 32; 32; 32; 32; 32; 71].

Example problem_86_test : problem_86_spec (string_of_nats input_nats) (string_of_nats output_nats).
Proof.
  unfold problem_86_spec.
  unfold anti_shuffle_impl.
  vm_compute.
  reflexivity.
Qed.