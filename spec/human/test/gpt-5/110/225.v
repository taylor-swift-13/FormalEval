Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* 两个输入列表均非空 *)
Definition problem_110_pre (lst1 lst2 : list nat) : Prop := lst1 <> [] /\ lst2 <> [].

Definition problem_110_spec (lst1 lst2 : list nat) (result : string) : Prop :=
  let odds_in_lst1 := List.length (List.filter Nat.odd lst1) in
  let evens_in_lst2 := List.length (List.filter Nat.even lst2) in
  if Nat.leb odds_in_lst1 evens_in_lst2
  then result = "YES"%string
  else result = "NO"%string.

Example problem_110_test :
  problem_110_pre [4; 7; 7; 7; 8; 13; 5; 1; 7; 7; 7] [4; 7; 7; 7; 8; 13; 5; 1; 7; 7; 7] /\
  problem_110_spec [4; 7; 7; 7; 8; 13; 5; 1; 7; 7; 7] [4; 7; 7; 7; 8; 13; 5; 1; 7; 7; 7] "NO"%string.
Proof.
  split.
  - unfold problem_110_pre; split; discriminate.
  - unfold problem_110_spec.
    simpl.
    reflexivity.
Qed.