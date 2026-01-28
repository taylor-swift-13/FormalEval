Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.

Definition largest_divisor_spec (n : nat) (result : nat) : Prop :=
  (result < n /\ n mod result = 0) /\ (forall x : nat, x < n -> n mod x = 0 -> x <= result).

Example test_case : largest_divisor_spec 3 1.
Proof.
  unfold largest_divisor_spec.
  split.
  - (* Verify result < n and n mod result = 0 *)
    split.
    + (* 1 < 3 *)
      repeat constructor.
    + (* 3 mod 1 = 0 *)
      reflexivity.
  - (* Verify maximality *)
    intros x Hlt Hdiv.
    (* Case analysis on x *)
    destruct x as [|x].
    + (* Case x = 0 *)
      (* 3 mod 0 = 3 (in Coq Nat), so Hdiv implies 3 = 0, which is false *)
      simpl in Hdiv.
      discriminate.
    + destruct x as [|x].
      * (* Case x = 1 *)
        (* Goal: 1 <= 1 *)
        apply le_n.
      * destruct x as [|x].
        -- (* Case x = 2 *)
           (* 3 mod 2 = 1, so Hdiv implies 1 = 0, which is false *)
           simpl in Hdiv.
           discriminate.
        -- (* Case x >= 3 *)
           (* Contradiction: x < 3 but x is structurally at least 3 *)
           (* Hlt : S (S (S x)) < 3 *)
           do 3 apply lt_S_n in Hlt.
           (* Hlt : x < 0, which is impossible *)
           inversion Hlt.
Qed.