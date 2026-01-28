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

Example test_case : is_simple_power_spec 9 3 true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _.
    (* We need to prove the disjunction. The case x=9, n=3 corresponds to the existential quantifier where k=2. *)
    right. right. right. right.
    exists 2.
    split.
    + (* Prove 0 <= 2 *)
      lia.
    + split.
      * (* Prove |3^2| <= |9| *)
        simpl. lia.
      * (* Prove 3^2 = 9 *)
        simpl. reflexivity.
  - intros _.
    (* Prove true = true *)
    reflexivity.
Qed.