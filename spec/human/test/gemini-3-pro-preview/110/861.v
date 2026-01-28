Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* 两个输入列表均非空 *)
Definition problem_110_pre (lst1 lst2 : list Z) : Prop := lst1 <> [] /\ lst2 <> [].

Definition problem_110_spec (lst1 lst2 : list Z) (result : string) : Prop :=
  let odds_in_lst1 := List.length (List.filter Z.odd lst1) in
  let evens_in_lst2 := List.length (List.filter Z.even lst2) in
  if Nat.leb odds_in_lst1 evens_in_lst2
  then result = "YES"%string
  else result = "NO"%string.

Example test_problem_110 : problem_110_spec [-1; 4; 6; 8; 7] [-1; 4; 6; 8; 7] "YES"%string.
Proof.
  (* Unfold the specification definition *)
  unfold problem_110_spec.
  
  (* Simplify the computation of list filtering, length, and boolean comparison *)
  simpl.
  
  (* The goal becomes "YES" = "YES", which is trivially true *)
  reflexivity.
Qed.