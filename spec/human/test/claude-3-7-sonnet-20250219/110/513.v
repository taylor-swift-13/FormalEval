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
  problem_110_spec [13; 5; 2; 5; 2; 8; 5; 1; 1; 0; 5] [13; 5; 2; 5; 2; 8; 5; 1; 1; 0; 5] "NO".
Proof.
  unfold problem_110_spec.
  simpl.
  (* Count odds in lst1 *)
  (* Odds in [13;5;2;5;2;8;5;1;1;0;5] are 13,5,5,5,1,1,5: total 7 odds *)
  (* Count evens in lst2 *)
  (* Evens in [13;5;2;5;2;8;5;1;1;0;5] are 2,2,8,0: total 4 evens *)
  (* Nat.leb 7 4 is false *)
  reflexivity.
Qed.