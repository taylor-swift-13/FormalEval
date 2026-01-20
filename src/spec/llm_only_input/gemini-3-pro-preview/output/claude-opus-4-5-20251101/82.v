Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Local Open Scope string_scope.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_prime_length_hello : prime_length_spec "Hello" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + (* Prove 5 >= 2 *)
      lia.
    + (* Prove forall d, 2 <= d -> d * d <= 5 -> ~(5 mod d = 0) *)
      intros d Hge Hsq.
      (* Case analysis on d *)
      destruct d as [|d]. { lia. } (* d = 0 *)
      destruct d as [|d]. { lia. } (* d = 1 *)
      destruct d as [|d].
      * (* d = 2 *)
        simpl. intro H. discriminate H.
      * (* d >= 3 *)
        simpl in Hsq.
        (* Prove contradiction: 9 <= d*d <= 5 *)
        assert (9 <= S (S (S d)) * S (S (S d))).
        {
          change 9 with (3 * 3).
          apply Nat.mul_le_mono; lia.
        }
        lia.
  - (* Prove is_prime 5 -> true = true *)
    intros _. reflexivity.
Qed.