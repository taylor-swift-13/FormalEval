
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.

Definition longest_spec (strings : list string) (result : option string) : Prop :=
  match strings with
  | nil => result = None
  | _ => exists maxlen maxstr,
         maxlen = fold_right (fun s max => max (length s) max) 0 strings /\
         In maxstr strings /\
         length maxstr = maxlen /\
         (forall s, In s strings -> length s <= maxlen) /\
         (forall s, In s strings -> length s = maxlen -> 
          exists prefix, strings = prefix ++ s :: nil \/ 
                       (In s prefix /\ result = Some maxstr)) /\
         result = Some maxstr
  end.
