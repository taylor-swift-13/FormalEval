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

Example test_prime_length_zyx : prime_length_spec "zyxwvutskraqpognmlkjihgfedcba" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + (* Prove 29 >= 2 *)
      lia.
    + (* Prove forall d, 2 <= d -> d * d <= 29 -> 29 mod d <> 0 *)
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
        destruct d3 as [| d4].
        { (* d = 3 *)
          simpl.
          intro Hmod.
          discriminate Hmod.
        }
        destruct d4 as [| d5].
        { (* d = 4 *)
          simpl.
          intro Hmod.
          discriminate Hmod.
        }
        destruct d5 as [| d6].
        { (* d = 5 *)
          simpl.
          intro Hmod.
          discriminate Hmod.
        }
        { (* d >= 6 *)
          (* If d >= 6, then d * d >= 36, which contradicts d * d <= 29 *)
          simpl in Hsq.
          assert (6 * 6 <= S (S (S (S (S (S d6))))) * S (S (S (S (S (S d6)))))) as H_lower_bound.
          {
            apply Nat.mul_le_mono; lia.
          }
          lia.
        }
  - intros _.
    reflexivity.
Qed.