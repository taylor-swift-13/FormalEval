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

Example test_exchange_1 :
  problem_110_spec [8;6;1;4;5;7;1;9;6;7;5;7] [8;6;1;4;5;7;1;9;6;7;5;7] "NO".
Proof.
  unfold problem_110_spec.
  simpl.
  (* Count odds in lst1 *)
  (* Odds in [8;6;1;4;5;7;1;9;6;7;5;7] are 1,5,7,1,9,7,5,7 → length = 8 *)
  (* Count evens in lst2 *)
  (* Evens in [8;6;1;4;5;7;1;9;6;7;5;7] are 8,6,4,6 → length = 4 *)
  (* Nat.leb 8 4 is false *)
  reflexivity.
Qed.