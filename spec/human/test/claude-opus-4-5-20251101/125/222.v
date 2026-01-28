Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(*
  辅助函数定义
*)

(* 1. 检查一个 (list ascii) 是否包含一个特定的 ascii 字符。 *)
Definition contains (l : list ascii) (c : ascii) : bool :=
  existsb (fun x => Ascii.eqb x c) l.

(* 2. 将一个 (list ascii) 按给定的分隔符拆分为一个单词列表 (list (list ascii))。*)
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

(* 3. 计算列表中字母序为奇数的小写字母的数量。
      'a' 的序数为 0，'b' 为 1，以此类推。 *)
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

Definition  problem_125_spec (input : string) (output : sum (list string) nat) : Prop :=
  let l := list_ascii_of_string input in
  if contains l " "%char then
    let res := split " "%char l in
    output = inl (map string_of_list_ascii res)
  else if contains l ","%char then
    let res := split ","%char l in
    output = inl (map string_of_list_ascii res)
  else
    output = inr (count_odd_lowercase l).

Open Scope string_scope.

Example test_problem_125 :
  problem_125_spec "This text contains no whitespaces but has commas,a period, and  odd-orspacesc,der lowercase letters such as bd, fhhj, and nprtvxz" (inl ("This" :: "text" :: "contains" :: "no" :: "whitespaces" :: "but" :: "has" :: "commas,a" :: "period," :: "and" :: "odd-orspacesc,der" :: "lowercase" :: "letters" :: "such" :: "as" :: "bd," :: "fhhj," :: "and" :: "nprtvxz" :: nil)).
Proof.
  unfold problem_125_spec.
  simpl.
  reflexivity.
Qed.