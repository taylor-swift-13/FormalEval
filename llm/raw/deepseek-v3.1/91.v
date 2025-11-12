
Require Import String List.
Require Import Ascii.

Definition is_bored_spec (S : string) (count : nat) : Prop :=
  count = length (filter (fun s => prefix "I " s) 
                      (map (fun s => trim s) 
                           (split "." (replace "!" "." (replace "?" "." S))))).
