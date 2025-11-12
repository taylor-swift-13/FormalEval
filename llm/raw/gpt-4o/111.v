
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Max.
Require Import Coq.Bool.Bool.
Require Import Coq.Maps.Map.
Require Import Coq.Structures.OrderedTypeEx.

Definition histogram_spec (test : string) (result : list (string * nat)) : Prop :=
  let words := filter (fun s => negb (String.eqb s "")) (String.split " " test) in
  let counts := fold_left (fun m word => 
                  let count := match Maps.find word m with
                               | Some c => c
                               | None => 0
                               end in
                  Maps.add word (count + 1) m) words (Maps.empty _) in
  let max_count := fold_left max (Maps.elements counts) 0 in
  result = filter (fun '(ch, c) => Nat.eqb c max_count) (Maps.elements counts).
