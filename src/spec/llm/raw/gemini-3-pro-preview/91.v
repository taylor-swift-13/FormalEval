
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Definition normalize_char (c : ascii) : ascii :=
  if (c =? "?") || (c =? "!") then "." else c.

Definition is_whitespace (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (n =? 32) || (n =? 9) || (n =? 10) || (n =? 13).

Fixpoint trim_head (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | h :: t => if is_whitespace h then trim_head t else l
  end.

Definition trim (l : list ascii) : list ascii :=
  trim_head (List.rev (trim_head (List.rev l))).

Fixpoint split_by_dot (l : list ascii) : list (list ascii) :=
  match l with
  | [] => [[]]
  | h :: t => 
      let rest := split_by_dot t in
      if h =? "." then [] :: rest
      else 
        match rest with
        | [] => [[h]]
        | r_h :: r_t => (h :: r_h) :: r_t
        end
  end.

Definition starts_with_I_space (l : list ascii) : bool :=
  match l with
  | "I" :: " " :: _ => true
  | _ => false
  end.

Definition is_bored_spec (S : string) (result : nat) : Prop :=
  let chars := string_to_list S in
  let normalized := map normalize_char chars in
  let raw_sentences := split_by_dot normalized in
  let trimmed_sentences := map trim raw_sentences in
  let bored_sentences := filter starts_with_I_space trimmed_sentences in
  result = length bored_sentences.
