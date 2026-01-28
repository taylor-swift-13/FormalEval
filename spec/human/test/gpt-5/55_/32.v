Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.

Inductive is_fib : nat -> Z -> Prop :=
  | fib_zero : is_fib 0 0%Z
  | fib_one  : is_fib 1 1%Z
  | fib_step : forall n res_n res_n1,
               is_fib n res_n ->
               is_fib (S n) res_n1 ->
               is_fib (S (S n)) (res_n1 + res_n)%Z.

Definition problem_55_pre (n : nat) : Prop := True.

Definition problem_55_spec (n : nat) (res : Z) : Prop :=
  is_fib n res.

Fixpoint fib_pair (n : nat) : Z * Z :=
  match n with
  | 0 => (0%Z, 1%Z)
  | S n' =>
      let p := fib_pair n' in
      let a := fst p in
      let b := snd p in
      (b, b + a)%Z
  end.

Lemma fib_pair_spec : forall n, is_fib n (fst (fib_pair n)) /\ is_fib (S n) (snd (fib_pair n)).
Proof.
  induction n as [|n [IHn IHSn]].
  - simpl. split; [apply fib_zero | apply fib_one].
  - simpl. split.
    + exact IHSn.
    + apply fib_step; [exact IHn | exact IHSn].
Qed.

Example problem_55_test_74 : problem_55_pre 74 /\ problem_55_spec 74 1304969544928657%Z.
Proof.
  split; [exact I|].
  pose proof (fib_pair_spec 74) as H.
  destruct H as [Hfst Hsnd].
  replace 1304969544928657%Z with (fst (fib_pair 74)) by (vm_compute; reflexivity).
  exact Hfst.
Qed.