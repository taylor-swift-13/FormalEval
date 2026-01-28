Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition problem_110_pre (lst1 lst2 : list Z) : Prop := lst1 <> [] /\ lst2 <> [].

Definition problem_110_spec (lst1 lst2 : list Z) (result : string) : Prop :=
  let odds_in_lst1 := List.length (List.filter Z.odd lst1) in
  let evens_in_lst2 := List.length (List.filter Z.even lst2) in
  if Nat.leb odds_in_lst1 evens_in_lst2
  then result = "YES"
  else result = "NO".

Example test_problem_110 : problem_110_spec [2; -1; 11; 8] [2; -1; 11; 8] "YES".
Proof.
  unfold problem_110_spec.
  simpl.
  reflexivity.
Qed.