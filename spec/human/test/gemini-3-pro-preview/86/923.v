Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition is_space_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  if Nat.eqb n 32 then true
  else if Nat.eqb n 9 then true
  else if Nat.eqb n 10 then true
  else if Nat.eqb n 12 then true
  else if Nat.eqb n 13 then true
  else false.

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

Definition FF := String (ascii_of_nat 12) EmptyString.

Definition input_str := 
  "bmqui 	
 	
 " ++ FF ++ "A B Cqui 	
 " ++ FF ++ "A B C   D E F     G H IprognraIInmming.r      k   D E F     G H I       " ++ FF ++ "A B C   D E Fkfox,     G H Ik".

Definition output_str := 
  "bimqu 	
 	
 " ++ FF ++ "A B Ciqu 	
 " ++ FF ++ "A B C   D E F     G H .IIIaggimmnnnoprrr      k   D E F     G H I       " ++ FF ++ "A B C   D E ,Ffkox     G H Ik".

Example problem_86_test : problem_86_spec input_str output_str.
Proof.
  unfold problem_86_spec.
  unfold anti_shuffle_impl.
  unfold input_str, output_str, FF.
  vm_compute.
  reflexivity.
Qed.