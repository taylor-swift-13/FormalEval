Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Fixpoint factorial (k : nat) : nat :=
  match k with
  | 0 => 1
  | S k' => (S k') * factorial k'
  end.

Fixpoint sum_1_to_i (i : nat) : nat :=
  match i with
  | 0 => 0
  | S i' => i + sum_1_to_i i'
  end.

Definition f_spec (n : nat) (l : list nat) : Prop :=
  length l = n /\
  (forall i, 1 <= i <= n ->
    nth (i-1) l 0 = 
      if Nat.even i then factorial i else sum_1_to_i i).

Example test_case_ok : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  unfold f_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct Hi as [Hi1 Hi2].
    destruct i as [|i0].
    + lia.
    + rewrite Nat.sub_1_r. simpl.
      assert (i0 <= 4) by lia.
      clear Hi1 Hi2.
      destruct i0 as [|i1].
      * (* i = 1 *)
        simpl. reflexivity.
      * (* i >= 2 *)
        destruct i1 as [|i2].
        -- (* i = 2 *)
           simpl. reflexivity.
        -- (* i >= 3 *)
           destruct i2 as [|i3].
           ++ (* i = 3 *)
              simpl. reflexivity.
           ++ (* i >= 4 *)
              destruct i3 as [|i4].
              ** (* i = 4 *)
                 simpl. reflexivity.
              ** (* i >= 5 *)
                 destruct i4 as [|i5].
                 --- (* i = 5 *)
                     simpl. reflexivity.
                 --- (* i >= 6, contradiction with i0 <= 4 *)
                     exfalso. lia.
Qed.