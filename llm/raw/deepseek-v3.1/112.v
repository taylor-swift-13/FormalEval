
Require Import String List Bool.

Definition reverse_delete_spec (s c : string) (result : string * bool) : Prop :=
  let filtered := filter (fun ch => negb (existsb (fun c_char => eqb ch c_char) c)) s in
  result = (filtered, eqb filtered (rev filtered)).
