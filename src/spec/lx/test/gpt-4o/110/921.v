Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition exchange_spec (lst1 lst2 : list nat) (result : string) : Prop :=
  let odds_in_lst1 := List.length (List.filter Nat.odd lst1) in
  let evens_in_lst2 := List.length (List.filter Nat.even lst2) in
  if Nat.leb odds_in_lst1 evens_in_lst2
  then result = "YES"%string
  else result = "NO"%string.

Example exchange_test :
  exchange_spec [11; 8; 2; 13] [11; 8; 2; 13] "YES".
Proof.
  unfold exchange_spec.
  simpl.
  reflexivity.
Qed.