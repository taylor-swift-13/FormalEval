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
  add_elements_spec [3; 200; 3; 40; 5000000; 39; 60; 7; 6; 8000; 9; 10; 7] 4 46.
Proof.
  unfold add_elements_spec.
  (* We use explicit splits to ensure the bullet structure is correct *)
  split.
  - (* Goal: 1 <= length arr *)
    simpl. lia.
  - split.
    + (* Goal: length arr <= 100 *)
      simpl. lia.
    + split.
      * (* Goal: 1 <= k *)
        lia.
      * split.
        -- (* Goal: k <= length arr *)
           simpl. lia.
        -- (* Goal: res = calculation *)
           unfold at_most_two_digitsb.
           simpl.
           reflexivity.
Qed.