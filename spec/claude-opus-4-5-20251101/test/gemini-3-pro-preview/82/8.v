Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope string_scope.

Definition is_prime (n : nat) : Prop :=
  n >= 2 /\ forall d : nat, 2 <= d -> d * d <= n -> ~(Nat.modulo n d = 0).

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  let len := String.length s in
  (result = true <-> is_prime len).

Example test_prime_length_wow : prime_length_spec "Wow" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + (* Prove 3 >= 2 *)
      lia.
    + (* Prove forall d, 2 <= d -> d * d <= 3 -> 3 mod d <> 0 *)
      intros d Hge2 Hsq.
      destruct d as [| d1].
      * (* d = 0 *) lia.
      * destruct d1 as [| d2].
        { (* d = 1 *) lia. }
        { (* d >= 2 *)
          (* Contradiction: d >= 2 -> d*d >= 4, but Hsq says d*d <= 3 *)
          assert (2 * 2 <= S (S d2) * S (S d2)).
          {
            apply Nat.mul_le_mono; lia.
          }
          lia.
        }
  - intros _.
    reflexivity.
Qed.