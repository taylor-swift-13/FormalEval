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
  - intro H.
    (* We need to prove that 16 is a power of 2. 
       This corresponds to the last branch of the disjunction. *)
    right. right. right. right.
    (* We instantiate the existential quantifier k with 4, since 2^4 = 16 *)
    exists 4.
    split.
    + (* Prove 0 <= 4 *)
      lia.
    + split.
      * (* Prove abs(2^4) <= abs(16) *)
        simpl. lia.
      * (* Prove 2^4 = 16 *)
        simpl. reflexivity.
  - (* The reverse direction: proving true = true is trivial *)
    intro H. reflexivity.
Qed.