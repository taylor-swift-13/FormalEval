Require Import List.
Require Import Arith.
Require Import Nat.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Definition generate_integers_spec (a b : nat) (evens : list nat) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (seq a (min (b + 1) 10 - a)).

Example test_generate_integers : 
  generate_integers_spec (Z.to_nat 987654321) (Z.to_nat 123456789) [].
Proof.
  unfold generate_integers_spec.
  destruct (Nat.leb_spec (Z.to_nat 987654321) (Z.to_nat 123456789)).
  - apply Z2Nat.inj_le in H; try lia.
  - assert (Hmin: 10 <= Z.to_nat 987654321 + 1).
    { apply Nat.le_trans with (m := Z.to_nat 987654321).
      - change 10 with (Z.to_nat 10).
        apply Z2Nat.inj_le; try lia.
      - apply Nat.le_add_r. }
    rewrite Nat.min_r; [|exact Hmin].
    assert (Hsub: 10 <= Z.to_nat 123456789).
    { change 10 with (Z.to_nat 10).
      apply Z2Nat.inj_le; try lia. }
    rewrite Nat.sub_0_le; [|exact Hsub].
    simpl. reflexivity.
Qed.