
Require Import Coq.Reals.Reals.
Require Import Coq.Strings.String.
Require Import Coq.Logic.Classical.

Inductive Value : Type :=
  | VInt : Z -> Value
  | VFloat : R -> Value
  | VString : string -> Value
  | VNone : Value.

Parameter parse_value : Value -> R.

Axiom parse_int : forall z : Z, parse_value (VInt z) = IZR z.
Axiom parse_float : forall r : R, parse_value (VFloat r) = r.
Axiom parse_string_replaces_comma : forall s : string, 
  exists r : R, parse_value (VString s) = r.

Definition compare_one_spec (a : Value) (b : Value) (result : Value) : Prop :=
  let num_a := parse_value a in
  let num_b := parse_value b in
  (num_a = num_b -> result = VNone) /\
  (num_a > num_b -> result = a) /\
  (num_a < num_b -> result = b).
