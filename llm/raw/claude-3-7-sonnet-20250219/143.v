
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Open Scope string_scope.
Open Scope nat_scope.

Fixpoint is_prime (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | 2 => true
  | _ =>
    let fix check_divisor d :=
      match d * d <=? n with
      | false => true
      | true =>
          if n mod d =? 0 then false else check_divisor (d + 1)
      end
    in check_divisor 2
  end.

Fixpoint split_words (s : string) (acc : list string) : list string :=
  match s with
  | EmptyString => rev acc
  | _ =>
    let i := index_of " " s 0 in
    if i =? length s then
      rev (s :: acc)
    else
      let w := substring 0 i s in
      let rest := substring (i + 1) (length s - (i + 1)) s in
      split_words rest (w :: acc)
  end
with index_of (c : string) (s : string) (start : nat) : nat :=
  match s with
  | EmptyString => 0
  | String ch s' =>
    if (String.eqb (String ch EmptyString) c)
    then start
    else index_of c s' (start + 1)
  end.

Fixpoint filter_prime_length_words (l : list string) : list string :=
  match l with
  | nil => nil
  | w :: ws =>
    if is_prime (length w)
    then w :: filter_prime_length_words ws
    else filter_prime_length_words ws
  end.

Definition words_in_sentence_spec (sentence result : string) : Prop :=
  let words := split_string_on_space sentence in
  let filtered := filter (fun w => is_prime (length w)) words in
  result = String.concat " " filtered.

(* Auxiliary definitions *)
Fixpoint split_string_on_space (s : string) : list string :=
  match s with
  | EmptyString => nil
  | _ =>
    let idx := index_space s 0 in
    if idx =? length s then
      cons s nil
    else
      (substring 0 idx s) :: split_string_on_space (substring (idx+1) (length s - (idx+1)) s)
  end
with index_space (s : string) (pos : nat) : nat :=
  match s with
  | EmptyString => pos
  | String c rest =>
    if String.eqb (String c EmptyString) " " then pos else index_space rest (pos + 1)
  end.

Fixpoint filter {A} (f : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if f x then x :: filter f xs else filter f xs
  end.

Fixpoint concat_strings (l : list string) : string :=
  match l with
  | [] => ""
  | [s] => s
  | s :: ss => s ++ " " ++ concat_strings ss
  end.

Definition String_concat := concat_strings.

Notation "String.concat sep l" := 
  (match l with
   | [] => ""
   | x :: xs => fold_left (fun acc y => acc ++ sep ++ y) xs x
   end) (at level 50).

