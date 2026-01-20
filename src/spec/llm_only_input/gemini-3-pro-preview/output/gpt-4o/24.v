Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition largest_divisor_spec (n : nat) (result : nat) : Prop :=
  (result < n /\ n mod result = 0) /\ (forall x : nat, x < n -> n mod x = 0 -> x <= result).

Example test_largest_divisor_3 : largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Prove 1 < 3 and 3 mod 1 = 0 *)
    split.
    + lia.
    + reflexivity.
  - (* Prove maximality *)
    intros x H_lt H_div.
    (* Perform case analysis on x since x < 3 *)
    destruct x as [| x1].
    + (* Case x = 0 *)
      (* In Coq, n mod 0 = n. So 3 mod 0 = 3. *)
      simpl in H_div.
      discriminate H_div.
    + destruct x1 as [| x2].
      * (* Case x = 1 *)
        lia.
      * destruct x2 as [| x3].
        -- (* Case x = 2 *)
           (* 3 mod 2 = 1 *)
           simpl in H_div.
           discriminate H_div.
        -- (* Case x >= 3 *)
           (* Contradicts H_lt *)
           lia.
Qed.