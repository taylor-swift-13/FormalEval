
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition planet :=
  string.

Definition planets_ordered : list planet :=
  ["Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune"].

Definition index_of (p : planet) : option nat :=
  let fix find_index l n :=
      match l with
      | [] => None
      | x :: xs => if String.eqb x p then Some n else find_index xs (S n)
      end
  in find_index planets_ordered 0.

Definition between_planets (planet1 planet2 : planet) (result : list planet) : Prop :=
  match index_of planet1, index_of planet2 with
  | Some i1, Some i2 =>
      let (start_idx, end_idx) := if Nat.leb i1 i2 then (i1, i2) else (i2, i1) in
      result = firstn (end_idx - start_idx - 1) (skipn (start_idx + 1) planets_ordered)
  | _, _ => result = []
  end.
