Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (b : bool) : Prop :=
  b = true <->
    (x = 1) \/ 
    (n = 0 /\ x = 0) \/ 
    (n = 1 /\ x = 1) \/ 
    (n = -1 /\ (x = 1 \/ x = -1)) \/
    exists k : Z,
      (0 <= k) /\
      (Z.abs (Z.pow n k) <= Z.abs x) /\
      (Z.pow n k = x).

Example test_case : is_simple_power_spec 16 2 true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _.
    (* We need to prove the disjunction. The case x=16, n=2 corresponds to the existential quantifier where k=4. *)
    right. right. right. right.
    exists 4.
    split.
    + (* Prove 0 <= 4 *)
      lia.
    + split.
      * (* Prove |2^4| <= |16| *)
        simpl. lia.
      * (* Prove 2^4 = 16 *)
        simpl. reflexivity.
  - intros _.
    (* Prove true = true *)
    reflexivity.
Qed.