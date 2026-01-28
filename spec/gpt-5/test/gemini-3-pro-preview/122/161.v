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
  add_elements_spec [111%Z; 1111%Z; 22%Z; 222%Z; 0%Z; 555%Z; 666%Z; 888%Z; 999%Z; 1000%Z; 2000%Z; 3030%Z; 5050%Z; 6000%Z; 7001%Z; 8000%Z; 9000%Z; 111%Z] 12 22%Z.
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