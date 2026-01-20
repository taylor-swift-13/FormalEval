
Require Import List.
Require Import String.

Definition planets : list string :=
  ["Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune"].

Definition bf_spec (planet1 planet2 : string) (result : list string) : Prop :=
  (In planet1 planets /\ In planet2 planets /\
   let i1 := index planet1 planets in
   let i2 := index planet2 planets in
   let indices := if i1 <=? i2 then (i1, i2) else (i2, i1) in
   result = firstn (snd indices - fst indices - 1) (skipn (fst indices + 1) planets))
  \/ (~In planet1 planets \/ ~In planet2 planets) /\ result = [].
