Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

(* Import ListNotations to allow [ ... ] syntax *)
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
  add_elements_spec [1; -2; -3; 41; 57; 76; 87; 88; 99] 3%nat (-4).
Proof.
  unfold add_elements_spec.
  (* We use explicit splits to ensure the proof structure matches the goal structure,
     avoiding "Wrong bullet" errors that can occur with repeat split. *)
  split.
  - (* Goal 1: 1 <= length arr *)
    simpl. lia.
  - split.
    + (* Goal 2: length arr <= 100 *)
      simpl. lia.
    + split.
      * (* Goal 3: 1 <= k *)
        lia.
      * split.
        -- (* Goal 4: k <= length arr *)
           simpl. lia.
        -- (* Goal 5: res = calculation *)
           simpl. reflexivity.
Qed.