Require Import Arith.
Require Import Lia.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  (* 1. output is a divisor of input *)
  input mod output = 0 /\

  (* 2. output is strictly less than input *)
  output < input /\

  (* 3. for any divisor i strictly less than input, i <= output *)
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Example test_case_24 : problem_24_spec 1000 500.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 1000 mod 500 = 0 *)
    reflexivity.
  - split.
    + (* Goal 2: 500 < 1000 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 1000 -> 1000 mod i = 0 -> i <= 500 *)
      intros i [Hpos Hlt] Hdiv.
      (* Convert mod to multiplication existence *)
      apply Nat.mod_divide in Hdiv; [|lia].
      destruct Hdiv as [k Hk].
      destruct k.
      * (* Case k = 0: 0 * i = 1000 -> 0 = 1000 *)
        simpl in Hk. discriminate.
      * destruct k.
        -- (* Case k = 1: 1 * i = 1000 -> i = 1000 *)
           simpl in Hk. rewrite Nat.add_0_r in Hk.
           subst. lia. (* Contradicts i < 1000 *)
        -- (* Case k >= 2 *)
           (* Proof by contradiction: assume i > 500 *)
           assert (Hi: i <= 500 \/ i > 500) by lia.
           destruct Hi as [|Hgt]; auto.
           (* If i > 500, then i >= 501. Since k >= 2, product >= 2 * 501 = 1002 *)
           assert (Hprod: S (S k) * i >= 2 * 501).
           { apply Nat.mul_le_mono; lia. }
           (* But product is 1000, so 1000 >= 1002, contradiction *)
           rewrite <- Hk in Hprod.
           simpl in Hprod.
           lia.
Qed.