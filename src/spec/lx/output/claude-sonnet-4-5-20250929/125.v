Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
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

Definition split_words_spec (input : list ascii) (output : sum (list (list ascii)) nat) : Prop :=
  if contains input " "%char then
    output = inl (split " "%char input)
  else if contains input ","%char then
    output = inl (split ","%char input)
  else
    output = inr (count_odd_lowercase input).

Example test_split_words :
  split_words_spec 
    ["H"%char; "e"%char; "l"%char; "l"%char; "o"%char; " "%char; 
     "w"%char; "o"%char; "r"%char; "l"%char; "d"%char; "!"%char]
    (inl [["H"%char; "e"%char; "l"%char; "l"%char; "o"%char]; 
          ["w"%char; "o"%char; "r"%char; "l"%char; "d"%char; "!"%char]]).
Proof.
  unfold split_words_spec.
  simpl.
  reflexivity.
Qed.