Require Import Nat.
Require Import List.
Require Import Factorial.
Require Import Lia.
Import ListNotations.

Definition problem_106_pre (n : nat) : Prop := True.

Definition problem_106_spec (n : nat) (l : list nat) : Prop :=
  let sum := fun i => Nat.div (i * (i + 1)) 2 in
  length l = n /\
  (forall i, 1 <= i -> i <= n -> nth_error l (i - 1) = Some (if even i then fact i else sum i)).

Example problem_106_test : problem_106_spec 8 [1; 2; 6; 24; 15; 720; 28; 40320].
Proof.
  unfold problem_106_spec.
  split.
  - simpl. reflexivity.
  - intros i H1 H2.
    destruct i as [|i']; [lia|].
    destruct i' as [|i''].
    + simpl. reflexivity.
    + destruct i'' as [|i'''].
      * simpl. reflexivity.
      * destruct i''' as [|i''''].
        -- simpl. reflexivity.
        -- destruct i'''' as [|i'''''].
           ++ simpl. reflexivity.
           ++ destruct i''''' as [|i''''''].
              ** simpl. reflexivity.
              ** destruct i'''''' as [|i'''''''].
                 --- simpl. reflexivity.
                 --- destruct i''''''' as [|i''''''''].
                     +++ simpl. reflexivity.
                     +++ destruct i'''''''' as [|i'''''''''].
                         *** simpl. reflexivity.
                         *** lia.
Qed.