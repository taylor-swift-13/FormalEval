
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.
Require Import Coq.Init.Nat.
Require Import Coq.Program.Basics.
Require Import Coq.micromega.Lra.
Require Import Coq.Bool.Bool.

Axiom parse_number : string -> R.

Axiom eq_dec_R : forall x y : R, {x = y} + {x <> y}.

Fixpoint string_replace (s old new_: string) : string :=
  (* This is a placeholder for string replacement that replaces all occurrences 
     of [old] with [new_] in [s]. The implementation detail is abstracted. *)
  s.

Definition to_number (v: string) : R :=
  parse_number (string_replace v "," ".").

Inductive input_value : Type :=
  | IInt : Z -> input_value
  | IFloat : R -> input_value
  | IStr : string -> input_value.

Definition input_to_string (v : input_value) : string :=
  match v with
  | IInt z => Z.to_string z
  | IFloat r => "" (* no simple standard conversion, assume incompatible for spec *)
  | IStr s => s
  end.

Definition input_to_number (v : input_value) : R :=
  match v with
  | IInt z => IZR z
  | IFloat r => r
  | IStr s => to_number s
  end.

Inductive output_value : Type :=
  | OVNone : output_value
  | OVVal : input_value -> output_value.

Definition compare_one_spec (a b : input_value) (res : output_value) : Prop :=
  let num_a := input_to_number a in
  let num_b := input_to_number b in
  (num_a = num_b /\ res = OVNone) \/
  (num_a <> num_b /\
   ((num_a > num_b /\ res = OVVal a) \/
    (num_b > num_a /\ res = OVVal b))) /\
  (* The return value must be of the same type as the input argument being returned *)
  match res with
  | OVNone => True
  | OVVal v => match v, a, b with
              | IInt _, IInt _, _ => v = a
              | IFloat _, IFloat _, _ => v = a
              | IStr _, IStr _, _ => v = a \/ v = b
              | _, _, _ => (* values returned must be same type as original variable returned *)
                 (v = a /\ num_a > num_b) \/ (v = b /\ num_b > num_a)
              end
  end.
