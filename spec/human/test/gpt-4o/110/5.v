Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition problem_110_pre (lst1 lst2 : list nat) : Prop := lst1 <> [] /\ lst2 <> [].

Definition problem_110_spec (lst1 lst2 : list nat) (result : string) : Prop :=
  let odds_in_lst1 := List.length (List.filter Nat.odd lst1) in
  let evens_in_lst2 := List.length (List.filter Nat.even lst2) in
  if Nat.leb odds_in_lst1 evens_in_lst2
  then result = "YES"%string
  else result = "NO"%string.

Example test_case_1 :
  problem_110_spec [5; 7; 3] [2; 6; 3] "NO".
Proof.
  unfold problem_110_spec.
  assert (H_odds_in_lst1: List.length (List.filter Nat.odd [5; 7; 3]) = 3).
  { simpl. reflexivity. }
  assert (H_evens_in_lst2: List.length (List.filter Nat.even [2; 6; 3]) = 2).
  { simpl. reflexivity. }
  rewrite H_odds_in_lst1, H_evens_in_lst2.
  simpl.
  reflexivity.
Qed.