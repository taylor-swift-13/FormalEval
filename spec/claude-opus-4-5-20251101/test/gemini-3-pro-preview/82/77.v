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

Example test_prime_length_custom : prime_length_spec "zyxwvutsrqpzyxwvutsrqponwmlkjihgfedcbaonmlkjihgfedcba" true.
Proof.
  unfold prime_length_spec.
  simpl.
  split.
  - intros _.
    unfold is_prime.
    split.
    + lia.
    + intros d Hge2 Hsq.
      destruct d as [|d]; [lia|].
      destruct d as [|d]; [lia|].
      destruct d as [|d]; [simpl; intro H; discriminate|]. (* d=2 *)
      destruct d as [|d]; [simpl; intro H; discriminate|]. (* d=3 *)
      destruct d as [|d]; [simpl; intro H; discriminate|]. (* d=4 *)
      destruct d as [|d]; [simpl; intro H; discriminate|]. (* d=5 *)
      destruct d as [|d]; [simpl; intro H; discriminate|]. (* d=6 *)
      destruct d as [|d]; [simpl; intro H; discriminate|]. (* d=7 *)
      simpl in Hsq.
      assert (8 * 8 <= S (S (S (S (S (S (S (S d))))))) * S (S (S (S (S (S (S (S d)))))))) by (apply Nat.mul_le_mono; lia).
      lia.
  - intros _.
    reflexivity.
Qed.