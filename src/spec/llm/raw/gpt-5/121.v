Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition solution_spec (lst : list Z) (sum : Z) : Prop :=
  lst <> [] /\
  sum =
    fold_right Z.add 0
      (map snd
        (filter (fun p =>
                   let '(i, x) := p in
                   andb (Nat.even i) (Z.odd x))
           (combine (seq 0 (length lst)) lst))).