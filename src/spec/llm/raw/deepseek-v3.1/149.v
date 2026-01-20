
Require Import List.
Require Import String.
Require Import Ascii.
Require Import Bool.
Require Import Arith.

Definition sorted_list_sum_spec (lst : list string) (result : list string) : Prop :=
  let filtered := filter (fun s => Nat.even (length s)) lst in
  exists sorted : list string,
    StronglySorted (fun s t => 
      if Nat.eqb (length s) (length t) 
      then leb s t 
      else leb (length s) (length t)) sorted /\
    Permutation filtered sorted /\
    result = sorted.
