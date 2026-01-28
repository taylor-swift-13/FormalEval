Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import ZArith.
Import ListNotations.

Definition problem_110_pre (lst1 lst2 : list Z) : Prop := lst1 <> [] /\ lst2 <> [].

Definition Z_odd (z : Z) : bool :=
  Z.odd z.

Definition Z_even (z : Z) : bool :=
  Z.even z.

Definition problem_110_spec (lst1 lst2 : list Z) (result : string) : Prop :=
  let odds_in_lst1 := List.length (List.filter Z_odd lst1) in
  let evens_in_lst2 := List.length (List.filter Z_even lst2) in
  if Nat.leb odds_in_lst1 evens_in_lst2
  then result = "YES"%string
  else result = "NO"%string.

Example test_problem_110 : problem_110_spec [(-1)%Z; 4%Z; 6%Z; 8%Z; 8%Z; 7%Z] [(-1)%Z; 4%Z; 6%Z; 8%Z; 8%Z; 7%Z] "YES"%string.
Proof.
  unfold problem_110_spec.
  simpl.
  reflexivity.
Qed.