
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.

(* Define a sum type to represent the mixed input types (int, float, string) *)
Inductive value : Type :=
| ValInt (z : Z)
| ValFloat (r : R)
| ValStr (s : string).

(* Parameter representing the parsing logic of strings to reals, 
   mimicking float(str(x).replace(",", ".")) *)
Parameter string_to_real : string -> R.

(* Helper function to convert the input value to a real number for comparison *)
Definition to_real (v : value) : R :=
  match v with
  | ValInt z => IZR z
  | ValFloat r => r
  | ValStr s => string_to_real s
  end.

Definition compare_one_spec (a b : value) (res : option value) : Prop :=
  let num_a := to_real a in
  let num_b := to_real b in
  (num_a = num_b -> res = None) /\
  (num_a > num_b -> res = Some a) /\
  (num_b > num_a -> res = Some b).
