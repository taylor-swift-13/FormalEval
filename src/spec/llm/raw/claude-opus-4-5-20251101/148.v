
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition planets : list string :=
  ["Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune"].

Definition is_valid_planet (p : string) : Prop :=
  In p planets.

Definition planet_index (p : string) : option nat :=
  let fix find_index (l : list string) (n : nat) : option nat :=
    match l with
    | [] => None
    | h :: t => if String.eqb h p then Some n else find_index t (S n)
    end
  in find_index planets 0.

Definition get_index (p : string) : nat :=
  match planet_index p with
  | Some n => n
  | None => 0
  end.

Definition slice (l : list string) (start finish : nat) : list string :=
  firstn (finish - start - 1) (skipn (S start) l).

Definition bf_spec (planet1 planet2 : string) (result : list string) : Prop :=
  (~ is_valid_planet planet1 \/ ~ is_valid_planet planet2 -> result = []) /\
  (is_valid_planet planet1 /\ is_valid_planet planet2 ->
    let i1 := get_index planet1 in
    let i2 := get_index planet2 in
    let low := Nat.min i1 i2 in
    let high := Nat.max i1 i2 in
    result = slice planets low high).
