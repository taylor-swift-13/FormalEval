
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition to_lower (c: ascii) : ascii :=
  if andb (Nat.leb 65 (nat_of_ascii c)) (Nat.leb (nat_of_ascii c) 90)
  then ascii_of_nat (nat_of_ascii c + 32)
  else c.

Fixpoint map_string (f: ascii -> ascii) (s: string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (f c) (map_string f rest)
  end.

Fixpoint elem {A} (eqb: A -> A -> bool) (x: A) (l: list A) : bool :=
  match l with
  | [] => false
  | y::ys => if eqb x y then true else elem eqb x ys
  end.

Fixpoint nodup_ascii (l: list ascii) : list ascii :=
  match l with
  | [] => []
  | x::xs => if elem ascii_dec x xs then nodup_ascii xs else x :: nodup_ascii xs
  end.

Definition string_to_list (s: string) : list ascii :=
  let fix go str acc :=
      match str with
      | EmptyString => rev acc
      | String c rest => go rest (c :: acc)
      end
  in go s [].

Definition count_distinct_characters_spec (string : string) (count : nat) : Prop :=
  count =
    length
      (nodup_ascii
        (map (to_lower)
          (string_to_list string))).
