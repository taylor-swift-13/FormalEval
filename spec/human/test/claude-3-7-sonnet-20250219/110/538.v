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
  problem_110_spec [1;4;7;7;8;13;12;1;7;7] [1;4;7;7;8;13;12;1;7;7] "NO".
Proof.
  unfold problem_110_spec.
  simpl.
  (* Count odds in lst1 *)
  (* Odds in [1;4;7;7;8;13;12;1;7;7] are 1,7,7,13,1,7,7, so length = 7 *)
  (* Count evens in lst2 *)
  (* Evens in [1;4;7;7;8;13;12;1;7;7] are 4,8,12, so length = 3 *)
  (* Nat.leb 7 3 is false *)
  reflexivity.
Qed.