Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.

Open Scope string_scope.
Open Scope char_scope.

Definition is_prime_hex (c : ascii) : bool :=
  match c with
  | "2" => true
  | "3" => true
  | "5" => true
  | "7" => true
  | "B" => true
  | "D" => true
  | _ => false
  end.

Fixpoint count_primes (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => 
      (if is_prime_hex c then 1 else 0) + count_primes rest
  end.

Definition hex_key_spec (num : string) (count : nat) : Prop :=
  count = count_primes num.

Example test_hex_key : hex_key_spec "753BDCEEFAD2020121721234567890ABCDEF12345BBAA22012334567890ABCDACDF11118872753BD159CEFF723BCCBB333A191BD7BB11ABCD22020DDBB2CC22EECEA5F3BDCEEFAD20201234512134567582290ABCDEFAACDF11118872159CEFF23BCCBBD4A006789CDEF04EFA12345BBB3137D1DDBB31CBAA202002E345BBAAA200456789C11ACDF1111887C2159CEFFACDF11118872159CEFF12345753BD6789123567890ABCDEF123B45BBAA22020A2202E23BCCBB333A11DDBCBBBD44ABCD2020DDB1ACDF11118872159CEFF23BCCBBD423456711ABCD2020753BDDDBBBCFFEEDDCCBBAA890ABCDEFA3137D1DDBB31CEFFEEDDCCBBAADEF0" 228.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.