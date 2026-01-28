Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition problem_110_spec (lst1 lst2 : list nat) (result : string) : Prop :=
  let odds_in_lst1 := List.length (List.filter Nat.odd lst1) in
  let evens_in_lst2 := List.length (List.filter Nat.even lst2) in
  if Nat.leb odds_in_lst1 evens_in_lst2
  then result = "YES"%string
  else result = "NO"%string.

Example test_exchange_case2 :
  problem_110_spec [1; 3; 5; 7; 7] [1; 3; 5; 7; 7] "NO"%string.
Proof.
  unfold problem_110_spec.
  simpl.
  reflexivity.
Qed.