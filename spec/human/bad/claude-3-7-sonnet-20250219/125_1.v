Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
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

Definition problem_125_spec (input : string) (output : sum (list string) nat) : Prop :=
  let l := list_ascii_of_string input in
  if contains l " "%char then
    let res := split " "%char l in
    output = inl (map string_of_list_ascii res)
  else if contains l ","%char then
    let res := split ","%char l in
    output = inl (map string_of_list_ascii res)
  else
    output = inr (count_odd_lowercase l).

Example test_split_hello_world :
  problem_125_spec "Hello world!" (inl ["Hello"; "world!"]).
Proof.
  unfold problem_125_spec.
  set (l := list_ascii_of_string "Hello world!").
  unfold contains.
  (* contains l " " = true *)
  (* list_ascii_of_string "Hello world!" = *)
  (* ['H'; 'e'; 'l'; 'l'; 'o'; ' '; 'w'; 'o'; 'r'; 'l'; 'd'; '!'] *)
  assert (H_contains_space : existsb (fun x => Ascii.eqb x " "%char) l = true).
  {
    unfold l.
    simpl.
    (* "Hello world!" in ascii list *)
    (* existsb returns true once it finds the space character *)
    (* Let's do induction on the string converted to list_ascii *)
    (* Alternatively, compute directly *)
    clear.
    compute.
    reflexivity.
  }
  rewrite H_contains_space.
  simpl.
  (* Prove split " " l = [["H";"e";"l";"l";"o"];["w";"o";"r";"l";"d";"!"]] *)
  unfold split.
  remember (l ++ [" "%char]) as s'.
  (* We'll analyze fold_left f s' ([],[]) *)
  (* Define f *)
  set (f := fun acc c =>
    let (res, cur) := acc in
    if Ascii.eqb c " "%char then
      match cur with
      | [] => (res, [])
      | _ :: _ => (res ++ [rev cur], [])
      end
    else
      (res, c :: cur)).
  (* We'll prove fold_left f s' ([], []) = ([["H";"e";"l";"l";"o"];["w";"o";"r";"l";"d";"!"]], []) *)
  (* unfold l *)
  subst l s'.
  simpl.
  (* The list is: ["H";"e";"l";"l";"o";" ";"w";"o";"r";"l";"d";"!";" "] *)
  (* Let's step through the fold manually: *)

  (* Start with acc = ([], []) *)
  (* c = 'H', not sep -> acc = ([], ['H']) *)
  (* c = 'e' -> acc = ([], ['e';'H']) *)
  (* c = 'l' -> acc = ([], ['l';'e';'H']) *)
  (* c = 'l' -> acc = ([], ['l';'l';'e';'H']) *)
  (* c = 'o' -> acc = ([], ['o';'l';'l';'e';'H']) *)
  (* c = ' ' -> sep and cur non-empty -> res = [] ++ [rev ['o';'l';'l';'e';'H']] = [["H";"e";"l";"l";"o"]] *)
  (* acc = ([["H";"e";"l";"l";"o"]], []) *)
  (* c = 'w' -> acc = ([["H";"e";"l";"l";"o"]], ['w']) *)
  (* c = 'o' -> acc = ([["H";"e";"l";"l";"o"]], ['o';'w']) *)
  (* c = 'r' -> acc = ([["H";"e";"l";"l";"o"]], ['r';'o';'w']) *)
  (* c = 'l' -> acc = ([["H";"e";"l";"l";"o"]], ['l';'r';'o';'w']) *)
  (* c = 'd' -> acc = ([["H";"e";"l";"l";"o"]], ['d';'l';'r';'o';'w']) *)
  (* c = '!' -> acc = ([["H";"e";"l";"l";"o"]], ['!';'d';'l';'r';'o';'w']) *)
  (* c = ' ' -> sep and cur non-empty -> res = previous ++ [rev ['!';'d';'l';'r';'o';'w']] *)
  (* rev ['!';'d';'l';'r';'o';'w'] = ['w';'o';'r';'l';'d';'!'] *)
  (* final res = [["H";"e";"l";"l";"o"];["w";"o";"r";"l";"d";"!"]] *)

  assert (Hfold :
    fold_left f
      ["H"%char;"e"%char;"l"%char;"l"%char;"o"%char;" "%char;"w"%char;"o"%char;"r"%char;"l"%char;"d"%char;"!"%char;" "%char]
      ([], []) =
    ([["H"%char;"e"%char;"l"%char;"l"%char;"o"%char]; ["w"%char;"o"%char;"r"%char;"l"%char;"d"%char;"!"%char]], [])).
  {
    (* Prove by repeated simplifications *)
    unfold f.
    simpl.
    (* Stepwise calculation can be done with compute *)
    compute.
    reflexivity.
  }
  rewrite Hfold.
  reflexivity.
Qed.