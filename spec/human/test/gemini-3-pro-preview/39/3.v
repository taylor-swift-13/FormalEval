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

Example problem_39_test_case : problem_39_spec 3 5.
Proof.
  unfold problem_39_spec.
  split.
  - (* Prove IsPrimeFib 5 *)
    unfold IsPrimeFib. split.
    + (* IsPrime 5 *)
      unfold IsPrime. split.
      * lia.
      * intros d Hmod.
        destruct d; [ simpl in Hmod; discriminate | ]. (* 0 *)
        destruct d; [ left; reflexivity | ]. (* 1 *)
        destruct d; [ simpl in Hmod; discriminate | ]. (* 2 *)
        destruct d; [ simpl in Hmod; discriminate | ]. (* 3 *)
        destruct d; [ simpl in Hmod; discriminate | ]. (* 4 *)
        destruct d; [ right; reflexivity | ]. (* 5 *)
        (* d > 5 *)
        assert (5 < S (S (S (S (S (S d)))))) by lia.
        apply Nat.mod_small in H.
        rewrite H in Hmod. discriminate.
    + (* IsFib 5 *)
      unfold IsFib. exists 5. simpl. reflexivity.
  - (* Prove set property for S = [2; 3] *)
    exists [2; 3].
    split.
    + (* length *)
      simpl. reflexivity.
    + split.
      * (* NoDup *)
        repeat constructor; intro H; inversion H; inversion H0.
      * (* Elements *)
        intros y. split.
        { (* In y [2; 3] -> y < 5 /\ IsPrimeFib y *)
          intro H.
          destruct H as [H2 | [H3 | Hfalse]].
          - (* y = 2 *)
            subst y. split. lia.
            unfold IsPrimeFib. split.
            + unfold IsPrime. split. lia.
              intros d Hmod.
              destruct d; [ simpl in Hmod; discriminate | ].
              destruct d; [ left; reflexivity | ].
              destruct d; [ right; reflexivity | ].
              assert (2 < S (S (S d))) by lia.
              apply Nat.mod_small in H. rewrite H in Hmod. discriminate.
            + unfold IsFib. exists 3. simpl. reflexivity.
          - (* y = 3 *)
            subst y. split. lia.
            unfold IsPrimeFib. split.
            + unfold IsPrime. split. lia.
              intros d Hmod.
              destruct d; [ simpl in Hmod; discriminate | ].
              destruct d; [ left; reflexivity | ].
              destruct d; [ simpl in Hmod; discriminate | ].
              destruct d; [ right; reflexivity | ].
              assert (3 < S (S (S (S d)))) by lia.
              apply Nat.mod_small in H. rewrite H in Hmod. discriminate.
            + unfold IsFib. exists 4. simpl. reflexivity.
          - inversion Hfalse.
        }
        { (* y < 5 /\ IsPrimeFib y -> In y [2; 3] *)
          intros [Hlt Hpf].
          unfold IsPrimeFib in Hpf. destruct Hpf as [Hp Hf].
          unfold IsPrime in Hp. destruct Hp as [Hgt1 Hdiv].
          (* Check y = 0, 1, 2, 3, 4 *)
          destruct y as [|y]. { lia. } (* 0 *)
          destruct y as [|y]. { lia. } (* 1 *)
          destruct y as [|y].
          - (* 2 *) left. reflexivity.
          - destruct y as [|y].
            + (* 3 *) right. left. reflexivity.
            + destruct y as [|y].
              * (* 4 *)
                (* 4 is not prime *)
                exfalso.
                specialize (Hdiv 2).
                assert (4 mod 2 = 0) by (simpl; reflexivity).
                apply Hdiv in H. destruct H; discriminate.
              * (* >= 5 *)
                lia.
        }
Qed.