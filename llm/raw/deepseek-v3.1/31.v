
Require Import ZArith.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  match n with
  | Z0 => result = false
  | Zpos x => 
      match x with
      | 1%positive => result = false
      | _ => 
          result = true <-> 
          (forall i : Z, 2 <= i < Zpos x -> ~ (Zpos x) mod i = 0) /\
          (Zpos x > 1)
      end
  | Zneg _ => result = false
  end.
