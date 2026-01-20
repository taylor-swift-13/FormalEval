
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition is_upper (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <=? n) && (n <=? 90).

Definition is_lower (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (97 <=? n) && (n <=? 122).

Fixpoint count_upper (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => (if is_upper c then 1 else 0) + count_upper rest
  end.

Fixpoint count_lower (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => (if is_lower c then 1 else 0) + count_lower rest
  end.

Definition strength (s : string) : Z :=
  Z.of_nat (count_upper s) - Z.of_nat (count_lower s).

Fixpoint max_strength (lst : list string) : option Z :=
  match lst with
  | [] => None
  | h :: t =>
    match max_strength t with
    | None => Some (strength h)
    | Some m => Some (Z.max (strength h) m)
    end
  end.

Fixpoint first_extension_with_strength (lst : list string) (str : Z) : option string :=
  match lst with
  | [] => None
  | h :: t =>
    if Z.eqb (strength h) str then Some h else first_extension_with_strength t str
  end.

Definition Strongest_Extension_spec (class_name : string) (extensions : list string) (res : string) : Prop :=
  exists max_str ext,
    max_strength extensions = Some max_str /\
    first_extension_with_strength extensions max_str = Some ext /\
    res = class_name ++ "." ++ ext.
