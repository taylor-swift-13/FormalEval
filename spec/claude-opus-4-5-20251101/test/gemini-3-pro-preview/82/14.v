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

Example test_prime_length_madam : prime_length_spec "Madam" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + (* Prove 5 >= 2 *)
      lia.
    + (* Prove forall d, 2 <= d -> d * d <= 5 -> 5 mod d <> 0 *)
      intros d Hge2 Hsq.
      (* Case analysis on d *)
      destruct d as [| d1].
      * (* d = 0 *) lia.
      * destruct d1 as [| d2].
        { (* d = 1 *) lia. }
        destruct d2 as [| d3].
        { (* d = 2 *)
          simpl.
          intro Hmod.
          discriminate Hmod.
        }
        { (* d >= 3 *)
          (* If d >= 3, then d * d >= 9, which contradicts d * d <= 5 *)
          simpl in Hsq.
          assert (3 * 3 <= S (S (S d3)) * S (S (S d3))) as H_lower_bound.
          {
            apply Nat.mul_le_mono; lia.
          }
          lia.
        }
  - intros _.
    reflexivity.
Qed.