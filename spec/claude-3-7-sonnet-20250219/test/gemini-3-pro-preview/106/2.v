Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
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

Example test_case : f_spec 7 [1; 2; 6; 24; 15; 720; 28].
Proof.
  unfold f_spec.
  split.
  - (* Check length *)
    simpl. reflexivity.
  - (* Check elements *)
    intros i [Hmin Hmax].
    destruct i.
    + (* i = 0 *)
      lia.
    + destruct i.
      * (* i = 1 *)
        simpl. reflexivity.
      * destruct i.
        -- (* i = 2 *)
           simpl. reflexivity.
        -- destruct i.
           ++ (* i = 3 *)
              simpl. reflexivity.
           ++ destruct i.
              ** (* i = 4 *)
                 simpl. reflexivity.
              ** destruct i.
                 --- (* i = 5 *)
                     simpl. reflexivity.
                 --- destruct i.
                     +++ (* i = 6 *)
                         simpl. reflexivity.
                     +++ destruct i.
                         *** (* i = 7 *)
                             simpl. reflexivity.
                         *** (* i >= 8 *)
                             lia.
Qed.