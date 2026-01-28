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

Example test_prime_length_long : prime_length_spec "ThequickbrownfoxjumpsoverthelazydogThequtheickbrownfoxjumpsoverthelazydogThequickbrownfoxjumpsoverthelazydogThequickbrownfoxjumpsoverthelazydogThequickbrownfoxjumpsoverthelazydog" false.
Proof.
  unfold prime_length_spec.
  (* Compute the length of the string. The length is 178. *)
  lazy [String.length].
  split.
  - intro H. discriminate H.
  - intro Hprime.
    unfold is_prime in Hprime.
    destruct Hprime as [_ Hforall].
    (* We proceed by contradiction. 178 is even, so it's not prime. *)
    (* We show that d=2 divides 178, contradicting the primality hypothesis. *)
    exfalso.
    apply (Hforall 2).
    + (* Prove 2 <= 2 *)
      lia.
    + (* Prove 2 * 2 <= 178 *)
      lia.
    + (* Prove 178 mod 2 = 0 *)
      reflexivity.
Qed.