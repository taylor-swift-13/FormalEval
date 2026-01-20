
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n) (n <=? 57).

Definition is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (andb (65 <=? n) (n <=? 90)) (andb (97 <=? n) (n <=? 122)).

Fixpoint count_digits (s : list ascii) : nat :=
  match s with
  | [] => 0
  | c :: rest => (if is_digit c then 1 else 0) + count_digits rest
  end.

Fixpoint split_on_dot (s : list ascii) : list (list ascii) :=
  match s with
  | [] => [[]]
  | c :: rest =>
    if (nat_of_ascii c =? 46)%nat then
      [] :: split_on_dot rest
    else
      match split_on_dot rest with
      | [] => [[c]]
      | h :: t => (c :: h) :: t
      end
  end.

Definition string_eq (s1 s2 : list ascii) : bool :=
  if (length s1 =? length s2)%nat then
    forallb (fun p => (nat_of_ascii (fst p) =? nat_of_ascii (snd p))%nat) (combine s1 s2)
  else false.

Definition valid_extension (ext : list ascii) : bool :=
  orb (string_eq ext ("t"%char :: "x"%char :: "t"%char :: nil))
      (orb (string_eq ext ("e"%char :: "x"%char :: "e"%char :: nil))
           (string_eq ext ("d"%char :: "l"%char :: "l"%char :: nil))).

Definition file_name_check_spec (file_name : list ascii) (result : string) : Prop :=
  let digit_count := count_digits file_name in
  let parts := split_on_dot file_name in
  (result = "Yes" <->
    (digit_count <= 3 /\
     length parts = 2 /\
     match parts with
     | [before_dot; after_dot] =>
       length before_dot > 0 /\
       match before_dot with
       | c :: _ => is_alpha c = true
       | [] => False
       end /\
       valid_extension after_dot = true
     | _ => False
     end)) /\
  (result = "No" <->
    ~(digit_count <= 3 /\
      length parts = 2 /\
      match parts with
      | [before_dot; after_dot] =>
        length before_dot > 0 /\
        match before_dot with
        | c :: _ => is_alpha c = true
        | [] => False
        end /\
        valid_extension after_dot = true
      | _ => False
      end)).
