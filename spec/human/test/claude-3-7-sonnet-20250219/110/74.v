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
  problem_110_spec [1;3;2;7;8;4;7] [1;3;2;7;8;4;7] "NO".
Proof.
  unfold problem_110_spec.
  simpl.
  (* Count odds in lst1: 1,3,7,7 -> length = 4 *)
  (* Count evens in lst2: 2,8,4 -> length = 3 *)
  (* Nat.leb 4 3 is false *)
  reflexivity.
Qed.