Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Import ListNotations.

Open Scope Z_scope.

Definition at_most_two_digitsb (z : Z) : bool :=
  Z.leb (Z.abs z) 99%Z.

Definition add_elements_spec (arr : list Z) (k : nat) (res : Z) : Prop :=
  Nat.le 1 (length arr) /\
  Nat.le (length arr) 100 /\
  Nat.le 1 k /\
  Nat.le k (length arr) /\
  res = fold_right Z.add 0%Z (filter at_most_two_digitsb (firstn k arr)).

Example test_add_elements : 
  add_elements_spec [1000; 8; 20; 300; 40000; 301; 100; 500; 10000; 6000; 70; 800; 10000; 10000; 70] 3 28.
Proof.
  unfold add_elements_spec.
  split.
  - simpl. lia.
  - split.
    + simpl. lia.
    + split.
      * lia.
      * split.
        -- simpl. lia.
        -- unfold at_most_two_digitsb.
           simpl.
           reflexivity.
Qed.