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

Example test_case_24 : problem_24_spec 7 1.
Proof.
  unfold problem_24_spec.
  split.
  - (* Goal 1: 7 mod 1 = 0 *)
    simpl. reflexivity.
  - split.
    + (* Goal 2: 1 < 7 *)
      lia.
    + (* Goal 3: forall i, 0 < i < 7 -> 7 mod i = 0 -> i <= 1 *)
      intros i [Hgt0 Hlt7] Hdiv.
      (* Since 0 < i < 7, i can be 1, 2, 3, 4, 5, 6 *)
      assert (i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) as Hcases by lia.
      destruct Hcases as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]].
      * (* Case i = 1 *)
        subst.
        lia.
      * (* Case i = 2 *)
        subst.
        simpl in Hdiv.
        discriminate Hdiv.
      * (* Case i = 3 *)
        subst.
        simpl in Hdiv.
        discriminate Hdiv.
      * (* Case i = 4 *)
        subst.
        simpl in Hdiv.
        discriminate Hdiv.
      * (* Case i = 5 *)
        subst.
        simpl in Hdiv.
        discriminate Hdiv.
      * (* Case i = 6 *)
        subst.
        simpl in Hdiv.
        discriminate Hdiv.
Qed.