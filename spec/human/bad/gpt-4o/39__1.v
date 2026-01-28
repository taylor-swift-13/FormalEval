Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Definition of primality *)
Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, d <> 1 -> d <> n -> n mod d <> 0).

(* Definition of Fibonacci sequence *)
Inductive fib_at : nat -> nat -> Prop :=
| fib_at_0 : fib_at 0 0
| fib_at_1 : fib_at 1 1
| fib_at_S : forall i a b,
    fib_at i a ->
    fib_at (S i) b ->
    fib_at (S (S i)) (a + b).

(* Definition of being a Fibonacci number *)
Definition IsFib (n : nat) : Prop := exists i : nat, fib_at i n.

(* Definition of Prime Fibonacci number *)
Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.

(* Pre-condition *)
Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

(* Specification definition *)
Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    length S = n - 1 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

(* Helper lemma to prove a number is a Fibonacci number *)
Lemma fib_example_3 : fib_at 3 2.
Proof.
  apply fib_at_S with (a := 1) (b := 1);
  [apply fib_at_1 | apply fib_at_S with (a := 0) (b := 1)];
  [apply fib_at_0 | apply fib_at_1].
Qed.

(* Example proof *)
Example prime_fib_example : problem_39_spec 1 2.
Proof.
  unfold problem_39_spec.
  split.
  - unfold IsPrimeFib. split.
    + unfold IsPrime. split; try lia.
      intros d Hd1 Hd2. assert (H: d = 1 \/ d = 2).
      { destruct d; try lia. destruct d; try lia.
        simpl. lia. }
      destruct H; auto.
    + unfold IsFib. exists 3. apply fib_example_3.
  - exists []. split.
    + simpl. lia.
    + split.
      * constructor.
      * intros y. split; intros H.
        -- inversion H.
        -- destruct H as [Hy Hpf].
           inversion Hy.
Qed.