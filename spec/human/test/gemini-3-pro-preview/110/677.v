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

Example test_problem_110 : problem_110_spec [3; 4; 13; 11; 5; 10; 11] [3; 4; 13; 11; 5; 10; 11] "NO"%string.
Proof.
  (* Unfold the specification definition *)
  unfold problem_110_spec.
  
  (* Simplify the computation:
     lst1 odds: [3; 13; 11; 5; 11] (length 5)
     lst2 evens: [4; 10] (length 2)
     Nat.leb 5 2 is false.
     Result becomes "NO".
  *)
  simpl.
  
  (* The goal becomes "NO" = "NO" *)
  reflexivity.
Qed.