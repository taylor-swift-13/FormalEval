Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition contains (l : list ascii) (c : ascii) : bool :=
  existsb (fun x => Ascii.eqb x c) l.

Definition split (sep : ascii) (s : list ascii) : list (list ascii) :=
  let s' := s ++ [sep] in
  let f (acc : list (list ascii) * list ascii) (c : ascii) :=
    let (res, current_word) := acc in
    if Ascii.eqb c sep then
      match current_word with
      | [] => (res, [])
      | _ :: _ => (res ++ [rev current_word], [])
      end
    else
      (res, c :: current_word)
  in
  let (res, _) := fold_left f s' ([], []) in
  res.

Definition count_odd_lowercase (l : list ascii) : nat :=
  let lowercase_ord (c : ascii) : nat :=
    match c with
    | "a"%char => 0 | "b"%char => 1 | "c"%char => 2 | "d"%char => 3
    | "e"%char => 4 | "f"%char => 5 | "g"%char => 6 | "h"%char => 7
    | "i"%char => 8 | "j"%char => 9 | "k"%char => 10 | "l"%char => 11
    | "m"%char => 12 | "n"%char => 13 | "o"%char => 14 | "p"%char => 15
    | "q"%char => 16 | "r"%char => 17 | "s"%char => 18 | "t"%char => 19
    | "u"%char => 20 | "v"%char => 21 | "w"%char => 22 | "x"%char => 23
    | "y"%char => 24 | "z"%char => 25
    | _ => 0
    end
  in
  let is_odd (n : nat) : bool :=
    negb (Nat.eqb (Nat.modulo n 2) 0)
  in
  let is_target_char (c : ascii) : bool :=
    is_odd (lowercase_ord c)
  in
  List.length (filter is_target_char l).

Definition problem_125_pre (input : string) : Prop := True.

Definition problem_125_spec (input : string) (output : sum (list string) Z) : Prop :=
  let l := list_ascii_of_string input in
  if contains l " "%char then
    let res := split " "%char l in
    output = inl (map string_of_list_ascii res)
  else if contains l ","%char then
    let res := split ","%char l in
    output = inl (map string_of_list_ascii res)
  else
    output = inr (Z.of_nat (count_odd_lowercase l)).

Example test_count_odd_lowercase :
  problem_125_spec "spaceshanhdslA"%string (inr 6%Z).
Proof.
  unfold problem_125_spec.
  vm_compute.
  reflexivity.
Qed.