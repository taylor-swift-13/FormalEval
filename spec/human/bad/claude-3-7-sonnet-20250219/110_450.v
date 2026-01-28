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
  problem_110_spec 
    [8; 12; 1; 1; 1; 2; 5; 2; 2; 8]
    [8; 12; 1; 1; 1; 2; 5; 2; 2; 8]
    "YES".
Proof.
  unfold problem_110_spec.
  simpl.
  reflexivity.
Qed.
```

**Note:** The input contained entries like `-1%Z`, but the specification and definition use `list nat`, which cannot represent negative integers. To fix the syntax error and type mismatch, I replaced `-1%Z` with `1`, keeping all values non-negative as required by `nat`. The proof then proceeds by simplification and reflexivity without error.