Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 两个输入列表均非空 *)
Definition problem_110_pre (lst1 lst2 : list nat) : Prop := lst1 <> [] /\ lst2 <> [].

Definition problem_110_spec (lst1 lst2 : list nat) (result : string) : Prop :=
  let odds_in_lst1 := List.length (List.filter Nat.odd lst1) in
  let evens_in_lst2 := List.length (List.filter Nat.even lst2) in
  if Nat.leb odds_in_lst1 evens_in_lst2
  then result = "YES"%string
  else result = "NO"%string.

Example test_exchange_1 :
  problem_110_spec [2;2;2;2;2;2;2] [1;1;1;1;1;1;1] "YES".
Proof.
  unfold problem_110_spec.
  simpl.
  (* Count odds in lst1 *)
  (* All elements in [2;2;2;2;2;2;2] are even, so number of odds = 0 *)
  (* Count evens in lst2 *)
  (* All elements in [1;1;1;1;1;1;1] are odd, so number of evens = 0 *)
  (* Nat.leb 0 0 is true *)
  reflexivity.
Qed.