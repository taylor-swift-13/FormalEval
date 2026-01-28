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
  problem_110_spec [3; 4; 2; 2; 4; 3] [3; 4; 2; 2; 4; 3] "YES".
Proof.
  unfold problem_110_spec.
  simpl.
  (* Count odds in lst1 *)
  (* Odds in [3;4;2;2;4;3] are 3 and 3, so length = 2 *)
  (* Count evens in lst2 *)
  (* Evens in [3;4;2;2;4;3] are 4, 2, 2, 4, so length = 4 *)
  (* Nat.leb 2 4 is true *)
  reflexivity.
Qed.