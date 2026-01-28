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

Example test_prime_length_xylophonist : prime_length_spec "xylophonist" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + lia.
    + intros d Hge2 Hsq.
      destruct d as [| d1].
      * lia.
      * destruct d1 as [| d2].
        { lia. }
        destruct d2 as [| d3].
        { simpl.
          intro Hmod.
          discriminate Hmod.
        }
        destruct d3 as [| d4].
        { simpl.
          intro Hmod.
          discriminate Hmod.
        }
        { simpl in Hsq.
          assert (4 * 4 <= S (S (S (S d4))) * S (S (S (S d4)))) as H_lower_bound.
          {
            apply Nat.mul_le_mono; lia.
          }
          lia.
        }
  - intros _.
    reflexivity.
Qed.