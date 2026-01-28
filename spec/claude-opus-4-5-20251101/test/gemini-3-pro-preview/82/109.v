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

Example test_prime_length_target : prime_length_spec "aabcbcdeabcdeLgdoOsvabcdeaabcdeaebcddefabacdabcdefgeadefggfgbcabcdeaefg" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + lia.
    + intros d Hge2 Hsq Hmod.
      assert (d < 9).
      {
        destruct (le_lt_dec 9 d).
        - assert (9 * 9 <= d * d) by (apply Nat.mul_le_mono; assumption).
          lia.
        - assumption.
      }
      destruct d as [|d]. { lia. }
      destruct d as [|d]. { lia. }
      destruct d as [|d]. { vm_compute in Hmod. discriminate. }
      destruct d as [|d]. { vm_compute in Hmod. discriminate. }
      destruct d as [|d]. { vm_compute in Hmod. discriminate. }
      destruct d as [|d]. { vm_compute in Hmod. discriminate. }
      destruct d as [|d]. { vm_compute in Hmod. discriminate. }
      destruct d as [|d]. { vm_compute in Hmod. discriminate. }
      destruct d as [|d]. { vm_compute in Hmod. discriminate. }
      lia.
  - intros _.
    reflexivity.
Qed.