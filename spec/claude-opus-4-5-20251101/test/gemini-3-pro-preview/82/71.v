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

Example test_prime_length_long : prime_length_spec "aabcbcdeabcabcddbefgdeabcddefgaeabcbcdefg" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + (* Prove 41 >= 2 *)
      lia.
    + (* Prove forall d, 2 <= d -> d * d <= 41 -> 41 mod d <> 0 *)
      intros d Hge2 Hsq.
      (* Case analysis on d up to sqrt(41) which is approx 6.4 *)
      destruct d as [| d]. { (* 0 *) lia. }
      destruct d as [| d]. { (* 1 *) lia. }
      destruct d as [| d]. { (* 2 *) simpl; discriminate. }
      destruct d as [| d]. { (* 3 *) simpl; discriminate. }
      destruct d as [| d]. { (* 4 *) simpl; discriminate. }
      destruct d as [| d]. { (* 5 *) simpl; discriminate. }
      destruct d as [| d]. { (* 6 *) simpl; discriminate. }
      (* d >= 7 *)
      (* If d >= 7, then d * d >= 49, which contradicts d * d <= 41 *)
      assert (7 * 7 <= S (S (S (S (S (S (S d)))))) * S (S (S (S (S (S (S d))))))) as H_lower_bound.
      {
        apply Nat.mul_le_mono; lia.
      }
      simpl in Hsq.
      lia.
  - intros _.
    reflexivity.
Qed.