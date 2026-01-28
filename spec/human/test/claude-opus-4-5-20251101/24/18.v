Require Import Arith.
Require Import Lia.

Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  input mod output = 0 /\
  output < input /\
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Lemma prime_73 : forall i, 2 <= i -> i < 73 -> 73 mod i <> 0.
Proof.
  intros i Hi_ge Hi_lt.
  destruct (Nat.eq_dec i 2) as [->|]; [simpl; lia|].
  destruct (Nat.eq_dec i 3) as [->|]; [simpl; lia|].
  destruct (Nat.eq_dec i 4) as [->|]; [simpl; lia|].
  destruct (Nat.eq_dec i 5) as [->|]; [simpl; lia|].
  destruct (Nat.eq_dec i 6) as [->|]; [simpl; lia|].
  destruct (Nat.eq_dec i 7) as [->|]; [simpl; lia|].
  destruct (Nat.eq_dec i 8) as [->|]; [simpl; lia|].
  assert (i >= 9) by lia.
  assert (i * i > 73) by nia.
  destruct (Nat.eq_dec (73 mod i) 0) as [Hdiv|Hndiv]; [|assumption].
  apply Nat.mod_divides in Hdiv; [|lia].
  destruct Hdiv as [k Hk].
  assert (k <> 0) by (intro; subst; lia).
  assert (k >= 1) by lia.
  assert (k < i) by nia.
  assert (k <= 8) by lia.
  destruct k; [lia|].
  destruct k; [simpl in Hk; lia|].
  destruct k; [simpl in Hk; lia|].
  destruct k; [simpl in Hk; lia|].
  destruct k; [simpl in Hk; lia|].
  destruct k; [simpl in Hk; lia|].
  destruct k; [simpl in Hk; lia|].
  destruct k; [simpl in Hk; lia|].
  lia.
Qed.

Example problem_24_test : problem_24_spec 73 1.
Proof.
  unfold problem_24_spec.
  split.
  - simpl. reflexivity.
  - split.
    + lia.
    + intros i [Hi_pos Hi_lt] Hi_div.
      destruct (Nat.eq_dec i 1) as [->|Hi_ne1].
      * lia.
      * assert (i >= 2) by lia.
        exfalso.
        apply (prime_73 i); assumption.
Qed.