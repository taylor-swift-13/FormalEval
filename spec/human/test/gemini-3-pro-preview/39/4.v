Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* fib i returns the i-th Fibonacci number *)
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

Definition IsFib (n : nat) : Prop := exists i : nat, fib i = n.

Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.

Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    length S = n - 1 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

Example problem_39_test_case : problem_39_spec 4 13.
Proof.
  unfold problem_39_spec.
  split.
  - (* Part 1: Prove IsPrimeFib 13 *)
    unfold IsPrimeFib. split.
    + (* IsPrime 13 *)
      unfold IsPrime. split.
      * (* 1 < 13 *)
        lia.
      * (* Divisors of 13 *)
        intros d Hmod.
        (* Check small divisors manually *)
        destruct d. { simpl in Hmod. discriminate. } (* 0 *)
        destruct d. { left. reflexivity. } (* 1 *)
        destruct d. { simpl in Hmod. discriminate. } (* 2 *)
        destruct d. { simpl in Hmod. discriminate. } (* 3 *)
        destruct d. { simpl in Hmod. discriminate. } (* 4 *)
        destruct d. { simpl in Hmod. discriminate. } (* 5 *)
        destruct d. { simpl in Hmod. discriminate. } (* 6 *)
        destruct d. { simpl in Hmod. discriminate. } (* 7 *)
        destruct d. { simpl in Hmod. discriminate. } (* 8 *)
        destruct d. { simpl in Hmod. discriminate. } (* 9 *)
        destruct d. { simpl in Hmod. discriminate. } (* 10 *)
        destruct d. { simpl in Hmod. discriminate. } (* 11 *)
        destruct d. { simpl in Hmod. discriminate. } (* 12 *)
        destruct d. { right. reflexivity. } (* 13 *)
        (* d >= 14 *)
        assert (Hgt: 13 < S (S (S (S (S (S (S (S (S (S (S (S (S (S d)))))))))))))) by lia.
        apply Nat.mod_small in Hgt.
        rewrite Hgt in Hmod.
        discriminate.
    + (* IsFib 13 *)
      unfold IsFib.
      exists 7.
      simpl. reflexivity.
  
  - (* Part 2: Prove the set property *)
    (* n=4, n-1=3. PrimesFib < 13 are 2, 3, 5. *)
    exists [2; 3; 5].
    split.
    + (* length [2;3;5] = 4 - 1 *)
      simpl. reflexivity.
    + split.
      * (* NoDup *)
        constructor.
        { intro H. simpl in H. destruct H as [H|H]; [discriminate|destruct H as [H|H]; [discriminate|contradiction]]. }
        constructor.
        { intro H. simpl in H. destruct H as [H|H]; [discriminate|contradiction]. }
        constructor.
        { intro H. simpl in H. contradiction. }
        constructor.
      * (* Elements check *)
        intros y. split.
        { (* In y S -> y < 13 /\ IsPrimeFib y *)
          intro H.
          destruct H as [H2 | [H3 | [H5 | Hfalse]]].
          - (* y = 2 *)
            rewrite <- H2. split. lia.
            unfold IsPrimeFib. split.
            + unfold IsPrime. split. lia.
              intros d Hd. destruct d. simpl in Hd. discriminate.
              destruct d. left. reflexivity.
              destruct d. right. reflexivity.
              assert (2 < S (S (S d))) by lia. apply Nat.mod_small in H. rewrite H in Hd. discriminate.
            + exists 3. simpl. reflexivity.
          - (* y = 3 *)
            rewrite <- H3. split. lia.
            unfold IsPrimeFib. split.
            + unfold IsPrime. split. lia.
              intros d Hd. destruct d. simpl in Hd. discriminate.
              destruct d. left. reflexivity.
              destruct d. simpl in Hd. discriminate.
              destruct d. right. reflexivity.
              assert (3 < S (S (S (S d)))) by lia. apply Nat.mod_small in H. rewrite H in Hd. discriminate.
            + exists 4. simpl. reflexivity.
          - (* y = 5 *)
            rewrite <- H5. split. lia.
            unfold IsPrimeFib. split.
            + unfold IsPrime. split. lia.
              intros d Hd. destruct d. simpl in Hd. discriminate.
              destruct d. left. reflexivity.
              destruct d. simpl in Hd. discriminate.
              destruct d. simpl in Hd. discriminate.
              destruct d. simpl in Hd. discriminate.
              destruct d. right. reflexivity.
              assert (5 < S (S (S (S (S (S d)))))) by lia. apply Nat.mod_small in H. rewrite H in Hd. discriminate.
            + exists 5. simpl. reflexivity.
          - inversion Hfalse.
        }
        { (* y < 13 /\ IsPrimeFib y -> In y S *)
          intro H. destruct H as [Hlt Hpf].
          destruct Hpf as [Hp Hf].
          destruct Hf as [k Hk].
          (* Bound k *)
          assert (Hmono: forall m, fib m <= fib (S m)).
          { intro m. destruct m. simpl. lia. simpl. lia. }
          assert (Hfib: forall m, 7 <= m -> 13 <= fib m).
          { intros m Hm. induction Hm. simpl. lia. specialize (Hmono m). lia. }
          assert (Hk_bound: k < 7).
          {
            destruct (le_lt_dec 7 k); try assumption.
            apply Hfib in l. rewrite Hk in l. lia.
          }
          (* Exhaustive check for k = 0..6 *)
          destruct k. (* 0 *) simpl in Hk. subst. unfold IsPrime in Hp. lia.
          destruct k. (* 1 *) simpl in Hk. subst. unfold IsPrime in Hp. lia.
          destruct k. (* 2 *) simpl in Hk. subst. unfold IsPrime in Hp. lia.
          destruct k. (* 3 -> 2 *) simpl in Hk. subst. left. reflexivity.
          destruct k. (* 4 -> 3 *) simpl in Hk. subst. right. left. reflexivity.
          destruct k. (* 5 -> 5 *) simpl in Hk. subst. right. right. left. reflexivity.
          destruct k. (* 6 -> 8 *) simpl in Hk. subst.
            (* 8 is not prime *)
            exfalso. unfold IsPrime in Hp. destruct Hp as [_ Hdiv].
            specialize (Hdiv 2). assert (8 mod 2 = 0) by reflexivity.
            apply Hdiv in H. destruct H; discriminate.
          (* k >= 7 contradiction *)
          lia.
        }
Qed.