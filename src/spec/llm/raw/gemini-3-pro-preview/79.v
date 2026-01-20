
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint pos_to_binary (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => (pos_to_binary p') ++ "0"
  | xI p' => (pos_to_binary p') ++ "1"
  end.

Definition Z_to_binary_string (n : Z) : string :=
  match n with
  | Z0 => "0"
  | Zpos p => pos_to_binary p
  | Zneg p => "" 
  end.

Definition decimal_to_binary_spec (decimal : Z) (result : string) : Prop :=
  result = "db" ++ (Z_to_binary_string decimal) ++ "db".
