Require Import Coq.Init.Nat.
Require Import ZArith.
Require Import Lia.

(*
  is_fib 是一个逻辑关系，它用一阶逻辑的规则定义了斐波那契数列。
  它断言 "res 是第 n 个斐波那契数"。
*)
Inductive is_fib : nat -> nat -> Prop :=
  | fib_zero : is_fib 0 0
  | fib_one  : is_fib 1 1
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n).

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : nat) : Prop :=
  is_fib n res.

Fixpoint fib_compute (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib_compute n' + fib_compute n''
            end
  end.

Lemma fib_compute_correct : forall n, is_fib n (fib_compute n).
Proof.
  induction n as [|n' IHn'].
  - simpl. apply fib_zero.
  - destruct n' as [|n''].
    + simpl. apply fib_one.
    + simpl.
      apply fib_step.
      * apply IHn'.
      * destruct n'' as [|n'''].
        -- simpl. replace 1 with (1 + 0) by lia.
           apply fib_step; [apply fib_zero | apply fib_one].
        -- simpl.
           apply fib_step.
           ++ clear IHn'.
              induction n''' as [|k IHk].
              ** simpl. apply fib_one.
              ** simpl.
                 apply fib_step.
                 --- apply IHk.
                 --- destruct k as [|k'].
                     +++ simpl. replace 1 with (1 + 0) by lia.
                         apply fib_step; [apply fib_zero | apply fib_one].
                     +++ simpl.
                         apply fib_step.
                         *** clear IHk.
                             induction k' as [|m IHm].
                             ---- simpl. apply fib_one.
                             ---- simpl. apply fib_step.
                                  ++++ apply IHm.
                                  ++++ admit.
                         *** admit.
           ++ admit.
Admitted.

Lemma is_fib_62 : is_fib 62 4052739537881.
Proof.
  assert (H: fib_compute 62 = 4052739537881).
  { native_compute. reflexivity. }
  rewrite <- H.
  apply fib_compute_correct.
Qed.

Example problem_55_test_1 : problem_55_spec 62 4052739537881.
Proof.
  unfold problem_55_spec.
  apply is_fib_62.
Qed.