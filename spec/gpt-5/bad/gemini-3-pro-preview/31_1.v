Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition divides (d n : Z) : Prop :=
  exists k : Z, n = d * k.

Definition is_prime_pred (n : Z) : Prop :=
  2 <= n /\ forall i : Z, 2 <= i <= Z.sqrt n -> ~ divides i n.

Definition is_prime_spec (n : Z) (b : bool) : Prop :=
  (b = true <-> is_prime_pred n) /\ (b = false <-> ~ is_prime_pred n).

Example test_prime_6 : is_prime_spec 6 false.
Proof.
  unfold is_prime_spec.
  split.
  - (* Part 1: false = true <-> is_prime_pred 6 *)
    split; intro H.
    + (* Left to Right: false = true implies anything *)
      discriminate H.
    + (* Right to Left: is_prime_pred 6 implies contradiction *)
      exfalso. (* Change goal to False to allow applying negations *)
      unfold is_prime_pred in H.
      destruct H as [_ Hcheck].
      (* Establish that 2 divides 6 *)
      assert (Hdiv: divides 2 6).
      { exists 3. reflexivity. }
      (* Establish that 2 is within the check range [2, sqrt(6)] *)
      assert (Hbound: 2 <= 2 <= Z.sqrt 6).
      { vm_compute. lia. }
      (* Apply the prime predicate to 2 *)
      specialize (Hcheck 2 Hbound).
      (* Hcheck is now ~ divides 2 6, which contradicts Hdiv *)
      contradiction.
  - (* Part 2: false = false <-> ~ is_prime_pred 6 *)
    split; intro H.
    + (* Left to Right: True implies ~ is_prime_pred 6 *)
      intro Hprime.
      unfold is_prime_pred in Hprime.
      destruct Hprime as [_ Hcheck].
      assert (Hdiv: divides 2 6).
      { exists 3. reflexivity. }
      assert (Hbound: 2 <= 2 <= Z.sqrt 6).
      { vm_compute. lia. }
      apply Hcheck in Hbound.
      contradiction.
    + (* Right to Left: ~ is_prime_pred 6 implies True *)
      reflexivity.
Qed.