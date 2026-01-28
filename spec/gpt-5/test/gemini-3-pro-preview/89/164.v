Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.

(* Open appropriate scopes for string literals and natural number notation *)
Open Scope string_scope.
Open Scope nat_scope.

(* --- Specification Definitions --- *)

Definition a_code : nat := nat_of_ascii (ascii_of_nat 97).
Definition z_code : nat := nat_of_ascii (ascii_of_nat 122).

Definition is_lowercase_ascii (c : ascii) : bool :=
  let n := nat_of_ascii c in Nat.leb a_code n && Nat.leb n z_code.

Definition rot4_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if is_lowercase_ascii c
  then ascii_of_nat (Nat.add a_code (Nat.modulo (Nat.add (Nat.sub n a_code) 4) 26))
  else c.

Fixpoint map_string (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (f c) (map_string f rest)
  end.

Definition encrypt_spec (s : string) (res : string) : Prop :=
  res = map_string rot4_ascii s.

(* --- Test Case Proof --- *)

Example test_encrypt_complex : encrypt_spec "heti    get a gf hellomyfrieonhello d" "lixm    kix e kj lippsqcjvmisrlipps h".
Proof.
  (* Unfold the specification definition *)
  unfold encrypt_spec.
  
  (* 
     Since the input and the expected output are concrete constants,
     and the function rot4_ascii is computable, we can simply rely on Coq's 
     computational capability (reduction) to verify the equality.
     
     reflexivity performs full normalization (simplification) of both sides 
     and checks if they are identical.
  *)
  reflexivity.
Qed.